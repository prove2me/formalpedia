-- Prove2me | Definitions.Def_FlowsNetworks_Graphs_MixedGraph
-- name    : FlowsNetworks_Graphs_MixedGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:04.539531+00:00
-- url     : https://prove2.me/theorems/f960c12e-9540-42f5-881b-88b8e95483e3
-- title:
--   Mixed graph $[N; \mathcal A]$, closed routes, unicursality, connectedness and arc counts
-- statement:
--   Following Chapter I (§1) and Chapter II (§7) of Ford and Fulkerson's *Flows in Networks*, this file sets up the objects of the unicursality theorem for mixed graphs.
--
--   1. A **mixed graph** $G = [N; \mathcal A]$ has a finite set $N$ of **nodes** and a set $\mathcal A$ of **arcs**, each of which is either **directed**, an ordered pair $(x, y)$ leading from $x$ to $y$, or **undirected**, an unordered pair $\{x, y\}$. No arc joins a node to itself, and there is at most one arc leading from a node to another: at most one directed arc $(x, y)$, at most one undirected arc $\{x, y\}$, and a pair of nodes joined by an undirected arc is not also joined by a directed arc. Both $(x, y)$ and $(y, x)$ may be directed arcs.
--   2. A **closed route** is a sequence
--   $$x_0,\ a_0,\ x_1,\ a_1,\ \dots,\ a_{m-1},\ x_m = x_0$$
--   of nodes $x_i$ and arcs $a_i$ in which each $a_i$ leads from $x_i$ to $x_{i+1}$: a directed arc is traversed with its direction, $a_i = (x_i, x_{i+1})$, while an undirected arc $a_i = \{x_i, x_{i+1}\}$ may be traversed either way. Nodes may repeat. A single node ($m = 0$) is a closed route.
--   3. $G$ is **unicursal** if there is a closed route in $G$ that contains each arc of $G$ once and only once, and each node of $G$ at least once. The graph with one node and no arcs is unicursal; a graph with two or more nodes and no arcs is not.
--   4. Two nodes are **adjacent** if some arc joins them, in either direction. $G$ is **connected** if $N$ is nonempty and any two nodes are joined by a path, a sequence of adjacent nodes (arcs may be traversed against their direction: weak connectedness).
--   5. The **degree** of a node $v$ is the number of arcs of $G$, directed and undirected together, incident with $v$.
--   6. For $X \subseteq N$ with complement $\bar X = N - X$: $d^+(X)$ is the number of directed arcs from $X$ to $\bar X$, $d^-(X)$ the number of directed arcs from $\bar X$ to $X$, and $u(X)$ the number of undirected arcs joining a node of $X$ to a node of $\bar X$.
--
--   **Formalization Note** Nodes form a `Fintype` with decidable equality. Directed arcs are a `Finset (N × N)` and undirected arcs a `Finset (Sym2 N)`; an arc of either kind is an element of `(N × N) ⊕ Sym2 N`. A closed route with $m$ arcs is a pair of maps `x : Fin (m+1) → N`, `a : Fin m → MixedArc N` with `x 0 = x m`; "each arc once and only once" is injectivity of `a` together with every arc of $G$ occurring. Connectedness is the reflexive-transitive closure of adjacency, plus nonemptiness of $N$ (the book's "exactly one connected class"). The rule that an undirected arc and a directed arc never join the same pair is the book's "at most one arc leading from any node to another" (Chapter I, p. 4) applied to mixed graphs.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, pp. 3–5 (§1: networks, mixed networks, no loops, at most one arc, chains and paths); Chapter II, pp. 40–42 (§7: unicursal graphs, closed route (7.1), connectedness)

import Mathlib

namespace FlowsNetworks.Graphs

/-- An arc of a mixed graph on the node set `N` (Ford–Fulkerson, *Flows in Networks*, Chapter I,
p. 4): either a directed arc, an ordered pair `(x, y)` leading from `x` to `y`, or an undirected
arc, an unordered pair `{x, y}`. -/
abbrev MixedArc (N : Type) : Type := (N × N) ⊕ Sym2 N

/-- A mixed linear graph `G = [N; 𝒜]` (Chapter I, p. 4; Chapter II, §7, p. 40): a finite node set
`N` together with a finite set of directed arcs (ordered pairs) and a finite set of undirected arcs
(unordered pairs). Arcs are loop-free, and there is at most one arc leading from a node to another
(Chapter I, p. 4): a directed set and an undirected set of pairs give at most one directed arc
`(x, y)` and at most one undirected arc `{x, y}`, and a pair joined by an undirected arc carries no
directed arc in either direction. Both `(x, y)` and `(y, x)` may be directed arcs. -/
structure MixedGraph (N : Type) [Fintype N] [DecidableEq N] where
  /-- the directed arcs `(x, y)` -/
  dirArcs : Finset (N × N)
  /-- the undirected arcs `{x, y}` -/
  undirArcs : Finset (Sym2 N)
  /-- no directed arc leads from a node to itself -/
  dir_loopless : ∀ p ∈ dirArcs, p.1 ≠ p.2
  /-- no undirected arc joins a node to itself -/
  undir_loopless : ∀ e ∈ undirArcs, ¬ e.IsDiag
  /-- a pair of nodes joined by an undirected arc is not also joined by a directed arc -/
  undir_not_dir : ∀ x y : N, s(x, y) ∈ undirArcs → (x, y) ∉ dirArcs

namespace MixedGraph

variable {N : Type} [Fintype N] [DecidableEq N]

/-- `a` is an arc of `G` (directed or undirected). -/
def IsArc (G : MixedGraph N) : MixedArc N → Prop
  | Sum.inl p => p ∈ G.dirArcs
  | Sum.inr e => e ∈ G.undirArcs

/-- Going from the node `x` to the node `y` along the arc `a` is a legal step: either `a` is the
directed arc `(x, y)` (a directed arc is traversed with its direction), or `a` is the undirected
arc `{x, y}` (traversed in either direction). -/
def Traverses (G : MixedGraph N) (x y : N) (a : MixedArc N) : Prop :=
  (a = Sum.inl (x, y) ∧ (x, y) ∈ G.dirArcs) ∨ (a = Sum.inr s(x, y) ∧ s(x, y) ∈ G.undirArcs)

/-- A closed route (7.1) `x₀, a₀, x₁, a₁, …, a_{m-1}, x_m = x₀` with `m` arcs (Chapter II, §7,
pp. 40–41): a sequence of nodes `x 0, …, x m` and arcs `a 0, …, a (m-1)` such that the route ends
where it starts and each arc `a i` leads from `x i` to `x (i+1)` (directed arcs with their
direction). Nodes may repeat. With `m = 0` the route is a single node, which the book stipulates
to be a closed route. -/
def IsClosedRoute (G : MixedGraph N) (m : ℕ) (x : Fin (m + 1) → N) (a : Fin m → MixedArc N) :
    Prop :=
  x 0 = x (Fin.last m) ∧ ∀ i : Fin m, G.Traverses (x i.castSucc) (x i.succ) (a i)

/-- `G` is unicursal (Chapter II, §7, p. 40): there is a closed route in `G` that contains each arc
of `G` once and only once (the arcs of the route are pairwise distinct and every arc of `G`
occurs), and each node of `G` at least once. -/
def Unicursal (G : MixedGraph N) : Prop :=
  ∃ (m : ℕ) (x : Fin (m + 1) → N) (a : Fin m → MixedArc N),
    G.IsClosedRoute m x a ∧ Function.Injective a ∧ (∀ e, G.IsArc e → ∃ i, a i = e) ∧
      ∀ v : N, ∃ i, x i = v

/-- Two nodes are adjacent when some arc of `G` joins them, in either direction (a path may
traverse a directed arc against its orientation, Chapter I, p. 5). -/
def Adj (G : MixedGraph N) (x y : N) : Prop :=
  (x, y) ∈ G.dirArcs ∨ (y, x) ∈ G.dirArcs ∨ s(x, y) ∈ G.undirArcs

/-- `G` is connected (Chapter II, §7, pp. 41–42): the nodes form exactly one connected class, i.e.
`N` is nonempty and any two nodes are joined by a path (arcs traversed in either direction;
weak connectedness, as in the book's footnote). -/
def Connected (G : MixedGraph N) : Prop :=
  Nonempty N ∧ ∀ x y : N, Relation.ReflTransGen G.Adj x y

/-- The number of arcs of `G` (directed and undirected together) incident with the node `v`. -/
def degree (G : MixedGraph N) (v : N) : ℕ :=
  (G.dirArcs.filter (fun p => p.1 = v ∨ p.2 = v)).card +
    (G.undirArcs.filter (fun e => v ∈ e)).card

/-- The number of directed arcs from `X` to `X̄ = N − X`. -/
def dirOut (G : MixedGraph N) (X : Finset N) : ℕ :=
  (G.dirArcs.filter (fun p => p.1 ∈ X ∧ p.2 ∉ X)).card

/-- The number of directed arcs from `X̄ = N − X` to `X`. -/
def dirIn (G : MixedGraph N) (X : Finset N) : ℕ :=
  (G.dirArcs.filter (fun p => p.1 ∉ X ∧ p.2 ∈ X)).card

/-- The number of undirected arcs joining `X` and `X̄ = N − X`, i.e. undirected arcs `{x, y}` with
`x ∈ X` and `y ∉ X`. -/
def undirJoining (G : MixedGraph N) (X : Finset N) : ℕ :=
  (G.undirArcs.filter (fun e => ∃ x ∈ X, ∃ y ∈ Xᶜ, e = s(x, y))).card

end MixedGraph

end FlowsNetworks.Graphs


