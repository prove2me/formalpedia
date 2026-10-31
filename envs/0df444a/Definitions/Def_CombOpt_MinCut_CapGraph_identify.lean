-- Prove2me | Definitions.Def_CombOpt_MinCut_CapGraph_identify
-- name    : CombOpt_MinCut_CapGraph_identify
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:53.770181+00:00
-- url     : https://prove2.me/theorems/f23dabdf-6aa3-4ccd-b1b2-ec9ab2fe3053
-- title:
--   Node identification $G_{vw}$
-- statement:
--   Let $v,w$ be distinct nodes of a capacitated graph $G=(V,E)$. The graph $G_{vw}$ is obtained by **identifying** $v$ with $w$:
--
--   1. its node set is $(V\setminus\{v,w\})\cup\{x\}$, where $x$ is a new node;
--   2. its edge set is $E\setminus\gamma(\{v,w\})$, where $\gamma(\{v,w\})$ is the set of edges with both ends in $\{v,w\}$;
--   3. for each such edge $e$ and end $p$ of $e$ in $G$, $p$ is an end of $e$ in $G_{vw}$ if $p\ne v,w$, and otherwise $x$ is an end of $e$;
--   4. the edges keep their capacities.
--
--   The operation may create parallel edges, and it creates no loop at $x$. It is the basic step of the node identification minimum cut algorithm.
--
--   **Formalization Note** The nodes of $G_{vw}$ are `some a` for $a\ne v,w$ and `none` for $x$; the edges are the edges of $G$ that do not have both ends in $\{v,w\}$ (a subtype of $E$). The construction is written for all $v,w$; the theorems that use it assume $v\ne w$, as the book does.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.5, p. 73 (PDF p. 82)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph

namespace CombOpt.MinCut

open Classical in
/-- **Node identification `G_vw`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.5, p. 73
(PDF p. 82): "Let v, w be distinct nodes. Then G_vw is obtained by identifying v with w. Namely, we
put V(G_vw) = (V\{v, w}) ∪ {x}, where x is a new node, and E(G_vw) = E\γ({v, w}); for each edge
e ∈ E and end p of e in G, p is an end of e in G_vw if p ≠ v, w, and otherwise x is an end of e in
G_vw. The edges of G_vw have the same capacities as they had in G."

The nodes of `G.identify v w` are `some a` for the nodes `a ≠ v, w` of `G`, and `none`, the new
node `x`. Its edges are the edges `e` of `G` not in `γ({v, w})`, i.e. not having both ends in
`{v, w}`; the ends of such an edge are those of `e` with `v` and `w` replaced by `x`, and its
capacity is `u_e`.

**Formalization Note.** The book requires `v ≠ w`; the construction is written for any `v, w`
and the theorems about it assume `v ≠ w`. `γ({v, w})` contains the edges joining `v` and `w` and the
loops at `v` or `w`, so `G_vw` has no loop at `x` (it keeps the loops of `G` at other nodes). An
edge of `G_vw` is an edge of `G` (a subtype element), so an edge set of `G_vw` is read as an edge
set of `G` through `Subtype.val`. -/
noncomputable def CapGraph.identify {V E : Type*} (G : CapGraph V E) (v w : V) :
    CapGraph (Option {a : V // a ≠ v ∧ a ≠ w}) {e : E // ¬ ∀ a ∈ G.ends e, a = v ∨ a = w} where
  ends e := Sym2.map (fun a => if h : a ≠ v ∧ a ≠ w then some ⟨a, h⟩ else none) (G.ends e.1)
  u e := G.u e.1

end CombOpt.MinCut


