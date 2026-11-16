-- Prove2me | Definitions.Def_PivotADO_OneHop_Supplement_Hopset
-- name    : PivotADO_OneHop_Supplement_Hopset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:41.849319+00:00
-- url     : https://prove2.me/theorems/8648cfc9-619e-479b-97a7-8b682ab61d33
-- title:
--   Definition 1 — $(k,\beta)$-hopsets and the $\beta$-hop distance $d^{\le\beta}_{G\cup F}$
-- statement:
--   Let $G=(V,E)$ be an undirected, unweighted simple graph with shortest-path distance $\delta_G$ (equal to $+\infty$ between different components). Let $\beta\ge1$ be an integer and $k\ge1$ a real number. A set $F$ of edges on $V$ is a **$(k,\beta)$-hopset** for $G$ when every edge $(x,y)\in F$ carries the weight $\delta_G(x,y)$ and, for all $u,v\in V$,
--
--   $$d^{\le\beta}_{G\cup F}(u,v)\le k\cdot\delta_G(u,v),$$
--
--   where $d^{\le\beta}_{G\cup F}(u,v)$ is the minimum weight of a $u$–$v$ path in $G\cup F$ that uses at most $\beta$ edges (an edge of $G$ has weight $1=\delta_G$). The **size** of the hopset is $|F|$; the edges of $G$ are not counted, and $F$ may contain edges of $G$.
--
--   The definition is the object of the hopset lower bounds (Theorems 3 and 4). The reverse inequality $\delta_G\le d^{\le\beta}_{G\cup F}$ holds automatically and is not part of the definition.
--
--   **Formalization Note** $F$ is a simple graph on $V$ (unordered, loopless edges) and its size is its number of edges. The $\beta$-hop distance is the infimum, in $[0,\infty]$, over walks of length at most $\beta$ in $G\sqcup F$ of the sum of $\delta_G$ over the walk's edges; walks and paths give the same minimum, the empty walk gives $0$ for $u=v$, and the infimum is $\infty$ when no walk of at most $\beta$ edges exists. The factor $k$ enters as `ENNReal.ofReal k`.
-- source:
--   Avi Kadria, Liam Roditty, STOC 2027 submission #584 (October 2026), Definition 1, p.5–6 (PDF pp. 6–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/584.pdf

import Definitions.Def_PivotADO_OneHop_Geometry

set_option autoImplicit false
open scoped Classical ENNReal
noncomputable section

namespace PivotADO.OneHop.Supplement

/-! Definition 1 ((k, β)-hopset), Kadria–Roditty, STOC 2027 submission #584
(October 2026), pp.5–6 (PDF 6–7). The hopset `F` is a set of unordered edges on the
vertex set, encoded as a simple graph; an edge `(x, y)` of `F` has weight `δ_G(x, y)`,
and an edge of `G` has weight `1 = δ_G(x, y)`. -/

/-- `d^{≤β}_{G∪F}(u, v)`: the minimum weight of a `u`–`v` walk in `G ∪ F` with at most
`β` edges, each edge `(x, y)` weighted by `δ_G(x, y)`. It is `⊤` when no such walk exists,
and `0` for `u = v` (the empty walk). Walks and paths give the same minimum. -/
def hopDistance {V : Type*} (G F : SimpleGraph V) (β : ℕ) (u v : V) : ℝ≥0∞ :=
  ⨅ (p : (G ⊔ F).Walk u v) (_ : p.length ≤ β),
    (p.darts.map fun d => distance G d.fst d.snd).sum

/-- `F` is a `(k, β)`-hopset for `G`: `d^{≤β}_{G∪F}(u, v) ≤ k · δ_G(u, v)` for all `u, v`.
The size of the hopset is `edgeCount F`; `F` may contain edges of `G`. -/
def IsHopset {V : Type*} (G F : SimpleGraph V) (k : ℝ) (β : ℕ) : Prop :=
  ∀ u v : V, hopDistance G F β u v ≤ ENNReal.ofReal k * distance G u v

end PivotADO.OneHop.Supplement


