-- Prove2me | Definitions.Def_FordFulkerson56_MinCut_IsChain
-- name    : FordFulkerson56_MinCut_IsChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:14:36.774417+00:00
-- url     : https://prove2.me/theorems/aaac91cc-4758-476f-bdbc-d2b41dc1cb5f
-- title:
--   Chain: a set of distinct arcs arranged as a self-avoiding path between two vertices
-- statement:
--   Let $N$ be a network (Ford–Fulkerson, p. 399). A **chain** joining vertices $u$ and $w$ is a set $C$ of distinct arcs that can be arranged as
--   $$\alpha_1(v_0v_1),\ \alpha_2(v_1v_2),\ \dots,\ \alpha_m(v_{m-1}v_m),\qquad v_0=u,\ v_m=w,$$
--   where the vertices $v_0,v_1,\dots,v_m$ are pairwise distinct (a chain does not intersect itself) and each arc $\alpha_i$ has end vertices $v_{i-1}$ and $v_i$, in either order. With $m=0$ this is the **null chain**, which joins $u$ to itself.
--
--   Two notions are defined:
--
--   1. a **chain walk** from $u$ to $w$: a list of arcs $(\alpha_1,\dots,\alpha_m)$ together with a list of vertices $(v_0,\dots,v_m)$ satisfying the conditions above;
--   2. a **chain** joining $u$ and $w$: a finite set of arcs that is the set of arcs of some chain walk from $u$ to $w$.
--
--   Chains joining the source and the sink are the routes along which flow is sent, and the objects a disconnecting set must meet.
--
--   **Formalization Note** Because arcs are undirected, the condition on the $i$-th arc allows either $(v_{i-1},v_i)=(\mathrm{tail},\mathrm{head})$ or the reverse. Both the arcs and the vertices of the walk are required to be pairwise distinct, as on the page. The paper's chain is a *set* of arcs that *can be arranged* in this way, hence the existential over arrangements.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 399, §1, definition of chain

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network

namespace FordFulkerson56.MinCut

variable {V E : Type*} [DecidableEq E]

/-- `IsChainWalk N u w p vs`: the list of arcs `p` together with the list of vertices `vs` is an
arrangement of a chain from `u` to `w` (Ford–Fulkerson, p. 399): `vs` has one more entry than `p`,
starts at `u` and ends at `w`; the arcs are distinct and the vertices are distinct; and the `i`-th arc
joins the `i`-th and `(i+1)`-th vertices, traversed in either direction (arcs are undirected). With
`p = []` and `vs = [u]` this is the null chain joining `u` and `u`. -/
def IsChainWalk (N : Network V E) (u w : V) (p : List E) (vs : List V) : Prop :=
  vs.length = p.length + 1 ∧ vs.head? = some u ∧ vs.getLast? = some w ∧
  vs.Nodup ∧ p.Nodup ∧
  ∀ (i : ℕ) (h : i < p.length),
    (vs[i]? = some (N.tail p[i]) ∧ vs[i + 1]? = some (N.head p[i])) ∨
    (vs[i]? = some (N.head p[i]) ∧ vs[i + 1]? = some (N.tail p[i]))

/-- A chain joining `u` and `w` (Ford–Fulkerson, p. 399): a set `C` of arcs which can be arranged as a
chain walk from `u` to `w`. -/
def IsChain (N : Network V E) (u w : V) (C : Finset E) : Prop :=
  ∃ (p : List E) (vs : List V), IsChainWalk N u w p vs ∧ p.toFinset = C

end FordFulkerson56.MinCut


