-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_netInflow
-- name    : CombOpt_MinCostFlow_Digraph_netInflow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:57.590023+00:00
-- url     : https://prove2.me/theorems/2ff3b065-5dd3-4b3e-95e1-c9077d7f69d1
-- title:
--   Net flow into a node $f_x(v)$
-- statement:
--   For a digraph $G=(V,E)$, a vector $x\in\mathbb R^E$ and a node $v$, the **net flow into** $v$ (the *excess* of $x$ at $v$) is
--
--   $$f_x(v)=\sum\bigl(x_e : h(e)=v\bigr)-\sum\bigl(x_e : t(e)=v\bigr).$$
--
--   A loop at $v$ appears in both sums and contributes nothing. Flow conservation constraints and demand constraints $f_x(v)=b_v$ are written with this quantity.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, p. 38 (PDF p. 47)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

namespace CombOpt.MinCostFlow

/-- **Net flow into a node, `f_x(v)`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, p. 38 (PDF p. 47): for x ∈ ℝ^E, the left-hand side of (3.1),
`Σ(x_wv : wv ∈ E) − Σ(x_vw : vw ∈ E)`, "is the *net flow into* v, or the *excess* of x at v, and we
abbreviate it to f_x(v)".

`G.netInflow x v` is the sum of `x e` over the arcs with head `v` minus the sum of `x e` over the
arcs with tail `v`.

**Formalization Note.** A loop at `v` is counted in both sums and so contributes `0`, as in the
book (a loop is in neither δ({v}) nor δ(V \ {v})). -/
def Digraph.netInflow {V E : Type*} [Fintype E] [DecidableEq V] (G : Digraph V E)
    (x : E → ℝ) (v : V) : ℝ :=
  (∑ e ∈ Finset.univ.filter (fun e => G.head e = v), x e) -
    ∑ e ∈ Finset.univ.filter (fun e => G.tail e = v), x e

end CombOpt.MinCostFlow


