-- Prove2me | Definitions.Def_PathCount2k_Supplement_Embedding
-- name    : PathCount2k_Supplement_Embedding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:19:54.583092+00:00
-- url     : https://prove2.me/theorems/a2e546b5-f1d7-4502-b8db-8cb309854326
-- title:
--   §3.2, Def. 3.2 — embeddings $\mathrm{Emb}(H,G)$, forest orientations, tree decompositions and treewidth
-- statement:
--   Let $H$ be a pattern graph on the vertex set $\{0,\dots,k-1\}$ and $G$ a host graph on $\{0,\dots,n-1\}$.
--
--   1. A **(non-induced) embedding** of an undirected graph $H$ into an undirected graph $G$ is an injective map $f:V(H)\to V(G)$ with $\{f(i),f(j)\}\in E(G)$ for every edge $\{i,j\}\in E(H)$; non-edges of $H$ are unconstrained. $\mathrm{Emb}(H,G)$ is the set of embeddings and $N=|\mathrm{Emb}(H,G)|$ counts maps, not subgraphs.
--   2. For directed graphs given by arc sets, an embedding is an injective $f$ with $(f(i),f(j))\in E(G)$ for every arc $(i,j)$ of the pattern; $N$ is again the number of such maps.
--   3. An **orientation of a forest** is an arc set without loops and without a pair of opposite arcs whose underlying undirected graph is acyclic.
--   4. A **tree decomposition** of $H$ (Definition 3.2) is a tree $T$ with a bag $B_x\subseteq V(H)$ for each node $x$ such that every vertex of $H$ lies in a bag, both endpoints of every edge lie in a common bag, and for every vertex $i$ the nodes whose bags contain $i$ induce a connected subtree of $T$. Its width is $\max_x|B_x|-1$, and $\mathrm{tw}(H)\le t$ means that some tree decomposition has all bags of size at most $t+1$.
--
--   These are the objects counted in Theorem 1.2: trees and forests (acyclic graphs), their orientations in directed hosts, and patterns of bounded treewidth.
--
--   **Formalization Note** Undirected graphs are Mathlib `SimpleGraph`s on `Fin k` / `Fin n`; directed graphs are arc sets `Finset (Fin k × Fin k)` as in the base mission's path count. The decomposition tree has node set `Fin m`; "treewidth at most $t$" is stated as "all bags have at most $t+1$ vertices" to avoid natural-number subtraction. `symArcs H` lists both orientations of each edge of an undirected graph.
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), §3.2, p.20 ("Write Emb(H, G) for the set of non-induced embeddings of H into G"), Definition 3.2, p.20; Theorem 1.2, p.2 (orientations of trees and forests); proof of Theorem 1.2, p.27 (directed version)

import Mathlib

namespace PathCount2k.Supplement

/-! # Embeddings, orientations of forests, tree decompositions and treewidth

Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026),
§3.2, pp.20–21.

**Formalization Note.** The pattern `H` has vertex set `Fin k`, the host `G` has vertex set
`Fin n`. Undirected graphs are Mathlib `SimpleGraph`s (no loops); directed graphs are arc sets
`Finset (Fin k × Fin k)` / `Finset (Fin n × Fin n)` as in the base mission's `PathCount2k.paths`. -/

/-- **Non-induced embeddings** `Emb(H, G)`, §3.2, p.20: "Write `Emb(H, G)` for the set of
non-induced embeddings of `H` into `G`, and let `N = |Emb(H, G)|`." An embedding is an injective
map `f : V(H) → V(G)` with `{f(i), f(j)} ∈ E(G)` for every edge `{i, j}` of `H`; non-edges of `H`
are unconstrained. -/
def IsEmb {k n : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)) (f : Fin k → Fin n) :
    Prop :=
  Function.Injective f ∧ ∀ i j, H.Adj i j → G.Adj (f i) (f j)

/-- `N = |Emb(H, G)|`, the number of embeddings (maps, not subgraphs: no division by
`|Aut(H)|`), §3.2, p.20. -/
noncomputable def embCount {k n : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)) : ℕ :=
  open Classical in (Finset.univ.filter fun f : Fin k → Fin n => IsEmb H G f).card

/-- **Directed embeddings** (end of the proof of Theorem 1.2, p.27: "Require separator assignments
to preserve arcs, … Every adjacency test then respects its specified direction"): injective maps
`f` with `(f(i), f(j)) ∈ E(G)` for every arc `(i, j)` of the pattern. -/
def IsDEmb {k n : ℕ} (PA : Finset (Fin k × Fin k)) (GA : Finset (Fin n × Fin n))
    (f : Fin k → Fin n) : Prop :=
  Function.Injective f ∧ ∀ a ∈ PA, (f a.1, f a.2) ∈ GA

/-- The number of directed embeddings of the pattern `PA` into the host `GA`. -/
noncomputable def dembCount {k n : ℕ} (PA : Finset (Fin k × Fin k))
    (GA : Finset (Fin n × Fin n)) : ℕ :=
  open Classical in (Finset.univ.filter fun f : Fin k → Fin n => IsDEmb PA GA f).card

/-- The underlying undirected graph of an arc set (loops dropped): `i ~ j` iff `i ≠ j` and
`(i, j)` or `(j, i)` is an arc (`SimpleGraph.fromRel`). -/
def underlying {k : ℕ} (PA : Finset (Fin k × Fin k)) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i j => (i, j) ∈ PA

/-- **An orientation of a forest** (Theorem 1.2, p.2: "arbitrary orientations of trees and forests
in directed host graphs"): an arc set with no loops and no pair of opposite arcs (each edge receives
exactly one direction) whose underlying undirected graph is acyclic. -/
def IsForestOrientation {k : ℕ} (PA : Finset (Fin k × Fin k)) : Prop :=
  (∀ a ∈ PA, a.1 ≠ a.2) ∧ (∀ i j, (i, j) ∈ PA → (j, i) ∉ PA) ∧ (underlying PA).IsAcyclic

/-- The arc set of an undirected graph: both orientations of every edge. -/
def symArcs {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] : Finset (Fin k × Fin k) :=
  Finset.univ.filter fun a => H.Adj a.1 a.2

/-- **Tree decomposition**, Definition 3.2, p.20: "A tree decomposition of `H` is a tree `T` with
a bag `B_x ⊆ V(H)` for each `x ∈ V(T)`, such that: 1. every vertex of `H` belongs to a bag;
2. every edge of `H` has both endpoints in a bag; 3. for every `i ∈ V(H)`, the nodes whose bags
contain `i` induce a connected subtree of `T`."

**Formalization Note.** The decomposition tree has node set `Fin m` (`IsTree` includes
nonemptiness). -/
structure TreeDecomp {k : ℕ} (H : SimpleGraph (Fin k)) where
  /-- number of decomposition nodes -/
  m : ℕ
  /-- the decomposition tree -/
  T : SimpleGraph (Fin m)
  isTree : T.IsTree
  /-- the bags -/
  bag : Fin m → Finset (Fin k)
  cover_vertex : ∀ i, ∃ x, i ∈ bag x
  cover_edge : ∀ i j, H.Adj i j → ∃ x, i ∈ bag x ∧ j ∈ bag x
  connected : ∀ i, (T.induce {x | i ∈ bag x}).Connected

/-- **Treewidth at most `t`**, Definition 3.2, p.20: "The width of the decomposition is
`max_x |B_x| − 1`. The treewidth `tw(H)` is the minimum width of a tree decomposition of `H`."
So `tw(H) ≤ t` iff some tree decomposition has all bags of size at most `t + 1`.

**Formalization Note.** Stated as `|B_x| ≤ t + 1` to avoid natural-number subtraction. -/
def TwLe {k : ℕ} (H : SimpleGraph (Fin k)) (t : ℕ) : Prop :=
  ∃ D : TreeDecomp H, ∀ x, (D.bag x).card ≤ t + 1

end PathCount2k.Supplement


