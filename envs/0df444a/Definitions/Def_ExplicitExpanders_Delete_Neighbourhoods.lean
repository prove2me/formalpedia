-- Prove2me | Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
-- name    : ExplicitExpanders_Delete_Neighbourhoods
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:55:56.496056+00:00
-- url     : https://prove2.me/theorems/a4588a5f-5e2f-4912-8cce-5dce31d84418
-- title:
--   Neighbourhoods of vertices and edges, layers $N_i$, cycle conditions (Section 3)
-- statement:
--   Let $H$ be a simple graph on a vertex set $V$, and write $\operatorname{dist}_H(v,w)\in\{0,1,2,\dots\}\cup\{\infty\}$ for the graph distance, which is $\infty$ when $v$ and $w$ lie in different components.
--
--   1. The **$k$-neighbourhood** of a vertex $v$ is $B_H(v,k) = \{w : \operatorname{dist}_H(v,w)\le k\}$.
--   2. The **$k$-neighbourhood of the edge (or pair) $uv$** is $B_H(\{u,v\},k) = \{w : \operatorname{dist}_H(u,w)\le k \text{ or } \operatorname{dist}_H(v,w)\le k\}$.
--   3. For $i \ge 0$, the **layer** $N_i$ (Lemma 3.2) is the set of vertices at distance exactly $i$ from $\{u,v\}$:
--   $$N_i = \{ w : \min(\operatorname{dist}_H(u,w), \operatorname{dist}_H(v,w)) = i\}.$$
--   In particular $N_0 = \{u,v\}$.
--   4. A set $S \subseteq V$ **contains no cycle** if the subgraph $H[S]$ induced on $S$ is acyclic (a forest).
--   5. A set $S \subseteq V$ (with $V$ finite) **contains at most one cycle** if the induced subgraph $H[S]$ has at most as many edges as vertices: $|E(H[S])| \le |S|$.
--
--   These are the neighbourhood notions of Section 3 of the paper. Definition 5 is applied only to balls $B_H(v,k)$, which induce connected subgraphs (every shortest path from $v$ to a vertex of the ball stays in the ball). A connected graph has at most one cycle exactly when its number of edges is at most its number of vertices (it is then a tree or a unicyclic graph), so on balls Definition 5 coincides with "contains at most one cycle". It is also the form in which the proof of Lemma 3.1 uses the hypothesis.
--
--   **Formalization Note** Distances are Mathlib's extended distance `SimpleGraph.edist` (values in `ℕ∞`), not `SimpleGraph.dist`, which is $0$ between different components. Containment of cycles always refers to the induced subgraph `H.induce S`. Edge and vertex counts use `Set.ncard`, which is meaningful because $V$ is finite.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, pp. 10–11, Section 3 (Lemma 3.1, Lemma 3.2: neighbourhoods and the sets N_i)

import Mathlib

namespace ExplicitExpanders.Delete

/-- The `k`-neighbourhood of a vertex `v` (Alon, arXiv:2003.11673v1, §3, p. 10): the vertices at
graph distance at most `k` from `v`. Distances are extended (`⊤` between components). -/
def ball {V : Type*} (H : SimpleGraph V) (v : V) (k : ℕ) : Set V :=
  {w | H.edist v w ≤ (k : ℕ∞)}

/-- The `k`-neighbourhood of the pair `{u, v}` (of the edge `uv`; §3, pp. 11 and 13): the vertices
at distance at most `k` from `u` or from `v`. -/
def edgeBall {V : Type*} (H : SimpleGraph V) (u v : V) (k : ℕ) : Set V :=
  {w | H.edist u w ≤ (k : ℕ∞) ∨ H.edist v w ≤ (k : ℕ∞)}

/-- `N_i` (Lemma 3.2, p. 11): the vertices at distance exactly `i` from the set `{u, v}`, i.e.
`min(dist(u, w), dist(v, w)) = i`. -/
noncomputable def layer {V : Type*} [Fintype V] (H : SimpleGraph V) (u v : V) (i : ℕ) :
    Finset V :=
  Finset.univ.filter fun w => min (H.edist u w) (H.edist v w) = (i : ℕ∞)

/-- The set `S` "contains no cycle": the subgraph of `H` induced on `S` is acyclic. -/
def NoCycleOn {V : Type*} (H : SimpleGraph V) (S : Set V) : Prop :=
  (H.induce S).IsAcyclic

/-- The set `S` "contains at most one cycle": the subgraph of `H` induced on `S` has at most as
many edges as vertices. For the connected sets this is applied to (balls), this is equivalent to
having at most one cycle. -/
def AtMostOneCycleOn {V : Type*} [Finite V] (H : SimpleGraph V) (S : Set V) : Prop :=
  (H.induce S).edgeSet.ncard ≤ S.ncard

end ExplicitExpanders.Delete


