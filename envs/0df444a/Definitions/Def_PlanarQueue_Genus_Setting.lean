-- Prove2me | Definitions.Def_PlanarQueue_Genus_Setting
-- name    : PlanarQueue_Genus_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:21:26.852228+00:00
-- url     : https://prove2.me/theorems/a03f8ecb-3861-4a76-bb54-2adf78e6ec0b
-- title:
--   pp. 3–12 — queue layouts, layerings, BFS layerings, BFS spanning trees and vertical paths
-- statement:
--   This file fixes the combinatorial objects of Dujmović, Joret, Micek, Morin, Ueckerdt and Wood, *Planar graphs have bounded queue-number*. All graphs are finite and simple, with vertex set $V$.
--
--   **Queue layouts** (pp. 3–4). Let $\preceq$ be a linear ordering of $V$. Two edges $vw$ and $xy$ with four distinct ends **nest** if, after renaming, $v \prec x \prec y \prec w$. A **queue** is a set of pairwise non-nested edges. A **$k$-queue layout** of $G$ is a linear ordering $\preceq$ of $V$ together with a partition $E_1, \dots, E_k$ of $E(G)$ into queues (some $E_i$ may be empty). We write
--   $$\operatorname{qn}(G) \le k$$
--   when $G$ has a $k$-queue layout.
--
--   **Layerings** (p. 7). A **layering** of $G$ is an ordered partition $(V_0, V_1, \dots)$ of $V$ (layers may be empty) such that the ends of every edge lie in the same or in consecutive layers. If $G_1, \dots, G_c$ are the components of $G$ and $r_j$ is a vertex of $G_j$, the layering with $V_i = \bigcup_j \{v \in V(G_j) : \operatorname{dist}_{G_j}(r_j, v) = i\}$ is a **BFS layering** of $G$.
--
--   **BFS spanning trees** (p. 7). For a connected graph $G$ and a vertex $r$, a **BFS spanning tree** rooted at $r$ is a spanning tree $T$ of $G$ with $\operatorname{dist}_T(r, v) = \operatorname{dist}_G(r, v)$ for every vertex $v$.
--
--   **Vertical paths** (p. 12). If $T$ is a tree rooted at $r$, a non-empty path $(x_1, \dots, x_p)$ in $T$ is **vertical** if the distances $\operatorname{dist}_T(x_i, r)$ increase by exactly one along the path: for some integer $d \ge 0$,
--   $$\operatorname{dist}_T(x_{i}, r) = d + i - 1 \qquad (1 \le i \le p).$$
--
--   These objects are the vocabulary of every statement of the mission: Lemma 18, Lemma 21, the $4g$-queue step and Theorem 2.
--
--   **Formalization Note** A linear ordering is an injective map $\mathrm{ord} : V \to \mathbb N$, and the queue assignment is a map from the edge set of $G$ (not from all unordered pairs) to $\{0, \dots, k-1\}$, so an edgeless graph has a $0$-queue layout. Nesting uses strict inequalities, so edges sharing an end never nest. A layering is its layer function $L : V \to \mathbb N$ ($v \in V_{L(v)}$). A BFS layering picks one root per component through a finite root set $R$; within a component, Mathlib's distance in $G$ equals the distance in that component. A vertical path is a list of vertices, indexed from $0$ with distance $d + i$; the page writes "for all $i \in \{0, \dots, p\}$" for a path $(x_1, \dots, x_p)$, read here so that the upper endpoint is at distance $d \ge 0$ (it may be the root). The queue-layout objects and the layering predicate are imported from the shared module `PlanarQueue.Planar.Setting`; this file adds the BFS layering (restated under `PlanarQueue.Genus` with the same body), BFS spanning trees and vertical paths.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, pp. 3–4 (§1, queue layouts), p. 7 (§2.1, layerings, BFS layerings, BFS spanning trees), p. 12 (§4, vertical paths)

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

namespace PlanarQueue.Genus

variable {V : Type}

/-- `L` is a BFS layering of `G` (p. 7): there is one root `r` in each connected component, and every
vertex `v` lies in layer `dist_G(r, v)` for the root `r` of its component. -/
def IsBFSLayering (G : SimpleGraph V) (L : V → ℕ) : Prop :=
  ∃ R : Finset V, (∀ v, ∃! r, r ∈ R ∧ G.Reachable r v) ∧
    ∀ r ∈ R, ∀ v, G.Reachable r v → L v = G.dist r v

/-- `T` is a BFS spanning tree of `G` rooted at `r` (p. 7): a spanning tree of `G` in which every
vertex has the same distance from `r` as in `G`. -/
def IsBFSTree (G T : SimpleGraph V) (r : V) : Prop :=
  T ≤ G ∧ T.IsTree ∧ ∀ v, T.dist r v = G.dist r v

/-- The list `l = [x₁, …, x_p]` is a vertical path in the tree `T` rooted at `r` (p. 12): it is
nonempty, consecutive entries are adjacent in `T`, and for some `d ≥ 0` the `i`-th entry
(counting from `0`) has distance `d + i` from `r` in `T`. -/
def IsVertical (T : SimpleGraph V) (r : V) (l : List V) : Prop :=
  l ≠ [] ∧ l.IsChain T.Adj ∧
    ∃ d : ℕ, ∀ (i : ℕ) (h : i < l.length), T.dist (l.get ⟨i, h⟩) r = d + i

/-- The vertex set `S` is the vertex set of a vertical path in `T` rooted at `r`. -/
def IsVerticalSet (T : SimpleGraph V) (r : V) (S : Set V) : Prop :=
  ∃ l : List V, IsVertical T r l ∧ {v | v ∈ l} = S

end PlanarQueue.Genus


