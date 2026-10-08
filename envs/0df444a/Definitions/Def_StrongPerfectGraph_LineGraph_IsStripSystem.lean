-- Prove2me | Definitions.Def_StrongPerfectGraph_LineGraph_IsStripSystem
-- name    : StrongPerfectGraph_LineGraph_IsStripSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:18:42.998821+00:00
-- url     : https://prove2.me/theorems/aa5df1ad-c68c-4f7b-953f-070c644e046c
-- title:
--   Rungs and J-strip systems
-- statement:
--   Let $J$ be $3$-connected and $G$ a graph. A **$J$-strip system** $(S, N)$ in $G$ consists of a set $S_{uv} = S_{vu} \subseteq V(G)$ for each edge $uv$ of $J$ and a set $N_v \subseteq V(G)$ for each vertex $v$ of $J$. For an edge $uv$ of $J$, a **$uv$-rung** is a path $R$ of $G$ with ends $s, t$ such that $V(R) \subseteq S_{uv}$, $s$ is the unique vertex of $R$ in $N_u$ and $t$ is the unique vertex of $R$ in $N_v$. The conditions are:
--
--   1. the sets $S_{uv}$ ($uv \in E(J)$) are pairwise disjoint;
--   2. for each $u \in V(J)$, $N_u \subseteq \bigcup\{S_{uv} : v \text{ adjacent to } u\}$;
--   3. for each $uv \in E(J)$, every vertex of $S_{uv}$ is in a $uv$-rung;
--   4. if $uv, wx \in E(J)$ with $u, v, w, x$ all distinct, there are no edges between $S_{uv}$ and $S_{wx}$;
--   5. if $uv, uw \in E(J)$ with $v \ne w$, then $N_u \cap S_{uv}$ is complete to $N_u \cap S_{uw}$, and there are no other edges between $S_{uv}$ and $S_{uw}$;
--   6. for each $uv \in E(J)$ there is a special $uv$-rung such that for every cycle $C$ of $J$, the sum of the lengths of the special $uv$-rungs for $uv \in E(C)$ has the same parity as $|V(C)|$.
--
--   Strip systems collect all alternative rungs of a line-graph appearance of $J$ in $G$.
--
--   **Formalization Note** $S$ is a function on all ordered pairs of vertices of $J$; only its values on edges matter, and symmetry is required on edges. A rung is a list oriented from its end in $N_u$ to its end in $N_v$; the special rungs are chosen so that the $vu$-rung is the reversed $uv$-rung. A cycle of $J$ is a cyclically listed subgraph cycle (not necessarily induced) with at least three vertices.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 98, §8, definition of J-strip system and uv-rung

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace StrongPerfectGraph.LineGraph

/-- A **cycle** of `J` (a subgraph, not necessarily induced), listed cyclically: at least three
distinct vertices, consecutive ones adjacent, and the last adjacent to the first. -/
def IsCycleList {W : Type*} (J : SimpleGraph W) (c : List W) : Prop :=
  3 ≤ c.length ∧ c.Nodup ∧ (c ++ c.take 1).IsChain J.Adj

/-- A **`uv`-rung** (p. 98): a path `R` of `G` (induced) with `V(R) ⊆ S_{uv}`, whose first vertex is
its unique vertex in `N_u` and whose last vertex is its unique vertex in `N_v`. -/
def IsRung {W V : Type*} (G : SimpleGraph V) (S : W → W → Set V) (N : W → Set V) (u v : W)
    (R : List V) : Prop :=
  StrongPerfectGraph.Main.IsInducedPath G R ∧ (∀ z ∈ R, z ∈ S u v) ∧
    (∀ z ∈ R, z ∈ N u ↔ R.head? = some z) ∧ (∀ z ∈ R, z ∈ N v ↔ R.getLast? = some z)

/-- `(S, N)` is a **`J`-strip system** in `G` (p. 98): sets `S_{uv} = S_{vu}` for the edges `uv` of
`J` and `N_v` for the vertices `v` of `J`, such that
* the `S_{uv}` are pairwise disjoint;
* `N_u ⊆ ⋃ {S_{uv} : v adjacent to u}`;
* every vertex of `S_{uv}` lies in a `uv`-rung;
* no edges between `S_{uv}` and `S_{wx}` when `u, v, w, x` are distinct;
* for `v ≠ w`, `N_u ∩ S_{uv}` is complete to `N_u ∩ S_{uw}` and there are no other edges between
  `S_{uv}` and `S_{uw}`;
* there is a special `uv`-rung for each edge `uv` such that for every cycle `C` of `J` the sum of
  the lengths of the special rungs of the edges of `C` has the parity of `|V(C)|`. -/
def IsStripSystem {W V : Type*} (J : SimpleGraph W) (G : SimpleGraph V) (S : W → W → Set V)
    (N : W → Set V) : Prop :=
  (∀ u v, J.Adj u v → S u v = S v u) ∧
  (∀ u v w x, J.Adj u v → J.Adj w x → s(u, v) ≠ s(w, x) → Disjoint (S u v) (S w x)) ∧
  (∀ u, ∀ z ∈ N u, ∃ v, J.Adj u v ∧ z ∈ S u v) ∧
  (∀ u v, J.Adj u v → ∀ z ∈ S u v, ∃ R : List V, IsRung G S N u v R ∧ z ∈ R) ∧
  (∀ u v w x, J.Adj u v → J.Adj w x → u ≠ w → u ≠ x → v ≠ w → v ≠ x →
    ∀ a ∈ S u v, ∀ b ∈ S w x, ¬ G.Adj a b) ∧
  (∀ u v w, J.Adj u v → J.Adj u w → v ≠ w →
    ∀ a ∈ S u v, ∀ b ∈ S u w, (G.Adj a b ↔ a ∈ N u ∧ b ∈ N u)) ∧
  (∃ R : W → W → List V,
    (∀ u v, J.Adj u v → IsRung G S N u v (R u v) ∧ R v u = (R u v).reverse) ∧
    ∀ c : List W, IsCycleList J c →
      ((c.zip (c.tail ++ c.take 1)).map (fun x => (R x.1 x.2).length - 1)).sum % 2 =
        c.length % 2)

end StrongPerfectGraph.LineGraph


