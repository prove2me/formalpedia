-- Prove2me | Definitions.Def_MetricGenerators_ConnectedJoin_TJoin
-- name    : MetricGenerators_ConnectedJoin_TJoin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:41.359026+00:00
-- url     : https://prove2.me/theorems/001e11a4-5c12-4552-8c7c-3d9ee8d77ef7
-- title:
--   T-joins (§3, p. 389): minimum and minimal T-joins; V(F), connected and tree edge sets, and the distance μ_F
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $T\subseteq V$. For a set $F\subseteq E$ of edges and a vertex $v$, write $\deg_F(v)$ for the number of edges of $F$ incident to $v$. Following Sebő and Tannier, $F$ is a **$T$-join** of $G$ if
--
--   $$F\subseteq E(G)\qquad\text{and}\qquad \deg_F(v)\ \text{is odd}\iff v\in T\quad\text{for every } v\in V.$$
--
--   1. A **minimum $T$-join** is a $T$-join $F$ with $|F|\le|F'|$ for every $T$-join $F'$ of $G$; its size is $\tau(G,T)$.
--   2. A **minimal $T$-join** is a $T$-join no proper subset of which is a $T$-join (inclusionwise minimality). Every minimum $T$-join is minimal.
--
--   For an edge set $F$, let $V(F)$ be the set of endpoints of edges of $F$, and consider the graph $(V(F),F)$.
--
--   3. $F$ is **connected** if the graph $(V(F),F)$ is connected; in particular $F\neq\emptyset$.
--   4. $F$ is a **tree** if the graph $(V(F),F)$ is a tree (connected and acyclic).
--   5. For $x,y\in V(F)$, $\mu_F(x,y)$ is the length of a shortest $x$–$y$ path in $(V(F),F)$.
--
--   These are the objects of §3.2 of the paper, which characterizes when a minimum $T$-join can be chosen connected.
--
--   **Formalization Note.** Edges are unordered pairs (`Sym2 V`) and $F$ is a `Finset`. The paper's standing hypotheses ($G$ connected, $|T|$ even) are hypotheses of the theorems, not part of the definition. Minimum is stated as "$|F|\le|F'|$ for every $T$-join $F'$", not as an infimum over $\mathbb N$. Connectivity and the tree property are those of the graph with edge set $F$ induced on $V(F)$, so the vertices outside $V(F)$ (isolated in the graph with edge set $F$ on all of $V$) do not count. $\mu_F(x,y)$ is computed as the distance in the graph with edge set $F$ on all of $V$, which agrees with the distance in $(V(F),F)$ for $x,y\in V(F)$, the only case used.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 389, §3 (T-join, minimal T-join, τ(G, T)); p. 391, §3.2 (connected T-join); p. 392, Lemma 2 (tree, V(F), μ_F)

import Mathlib
import Definitions.Def_MetricGenerators_FewComponents_TJoin

namespace MetricGenerators.ConnectedJoin

/-- An (inclusionwise) minimal `T`-join (Sebő and Tannier 2004, §3, p. 389: "a minimal T-join is
the disjoint union of |T|/2 paths"): a `T`-join no proper subset of which is a `T`-join. Every
minimum `T`-join is minimal. -/
def IsMinimalTJoin {V : Type*} [DecidableEq V] (G : SimpleGraph V) (T : Finset V)
    (F : Finset (Sym2 V)) : Prop :=
  MetricGenerators.FewComponents.IsTJoin G T F ∧ ∀ F' : Finset (Sym2 V), F' ⊆ F → MetricGenerators.FewComponents.IsTJoin G T F' → F' = F

/-- `F` is connected (Sebő and Tannier 2004, §3, p. 389 and §3.2, p. 391: "a minimum T-join that
is also connected"): the graph `(V(F), F)` is connected.

**Formalization Note.** This is the graph `edgeGraph F` induced on `V(F)`, **not** `edgeGraph F`
on all of `V` (in which every vertex outside `V(F)` is an isolated vertex). Mathlib's
`Connected` requires a nonempty vertex set, so the empty edge set is not connected. -/
def IsConnectedEdgeSet {V : Type*} (F : Finset (Sym2 V)) : Prop :=
  ((MetricGenerators.FewComponents.edgeGraph F).induce (MetricGenerators.FewComponents.edgeSupport F)).Connected

/-- `F` is a tree (Sebő and Tannier 2004, §3.2, Lemma 2, p. 392): the graph `(V(F), F)` is a tree,
i.e. connected and acyclic.

**Formalization Note.** As in `IsConnectedEdgeSet`, the graph is `edgeGraph F` induced on `V(F)`.
-/
def IsTreeEdgeSet {V : Type*} (F : Finset (Sym2 V)) : Prop :=
  ((MetricGenerators.FewComponents.edgeGraph F).induce (MetricGenerators.FewComponents.edgeSupport F)).IsTree

/-- μ_F(x, y): the distance between `x` and `y` in the graph `(V(F), F)` (Sebő and Tannier 2004,
Lemma 2, p. 392; μ_G is defined on p. 383 as the length of a shortest path).

**Formalization Note.** Computed as `(MetricGenerators.FewComponents.edgeGraph F).dist x y`. For `x, y ∈ V(F)` this is the
distance in `(V(F), F)`: every vertex of a walk of `edgeGraph F` between two vertices of `V(F)`
lies in `V(F)`. It is only used for `x, y ∈ V(F)`. -/
noncomputable def edgeDist {V : Type*} (F : Finset (Sym2 V)) (x y : V) : ℕ :=
  (MetricGenerators.FewComponents.edgeGraph F).dist x y

end MetricGenerators.ConnectedJoin


