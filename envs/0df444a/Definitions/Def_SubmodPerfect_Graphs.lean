-- Prove2me | Definitions.Def_SubmodPerfect_Graphs
-- name    : SubmodPerfect_Graphs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:15.513005+00:00
-- url     : https://prove2.me/theorems/04112984-dad7-4bc5-b6a8-46cdfefeaa70
-- title:
--   Neighbourhoods, components, balls $N^d[v]$, even sets, balanced and $(w,k,c,d)$-even set separators
-- statement:
--   All graphs are finite and simple. For a vertex set $U\subseteq V(G)$ the induced subgraph $G[U]$ is represented by $U$ itself, and the following notions are taken inside $G[U]$ ($U=V(G)$ gives $G$).
--
--   1. $N(X)$ is the set of vertices outside $X$ with a neighbour in $X$, and $N[X]=N(X)\cup X$.
--   2. A **connected component** of $G[U]$ is a nonempty set $D\subseteq U$ inducing a connected graph with no edge from $D$ to $U\setminus D$.
--   3. $N^d[v]$ is the set of vertices of $U$ joined to $v$ by a walk of length at most $d$ inside $U$; a set $X$ is **$d$-bounded** if $X\subseteq N^d[v]$ for some $v\in U$.
--   4. A **path** from $x$ to $y$ is an induced path $x=p_0\text{-}p_1\text{-}\cdots\text{-}p_k=y$; its length is $k$.
--   5. $\{x,y\}$ is an **even pair** if $x\ne y$ and every path of $G[U]$ from $x$ to $y$ has even length. A set $X\subseteq U$ is an **even set** if every two distinct vertices of $X$ form an even pair.
--   6. $(L_1,\dots,L_k)$ is a **$k$-iterated even set** if the $L_i$ are pairwise disjoint subsets of $U$ and each $L_i$ is an even set of $G[U]\setminus\bigcup_{j<i}L_j$.
--   7. For $w:V(G)\to\mathbb R$, $w(X)=\sum_{x\in X}w(x)$. A **weight function** takes values in $[0,1]$, and the **uniform weight function** of a nonempty $X$ is $1/|X|$ on $X$ and $0$ elsewhere.
--   8. $X\subseteq U$ is a **$(w,c)$-balanced separator** if every component $D$ of $G[U]\setminus X$ has $w(D)\le c$.
--   9. $L=(L_1,\dots,L_k)$ is a **$(w,k,c,d)$-even set separator** of $G$ if it is a $k$-iterated even set of $G$ and every component $D$ of $G\setminus\bigcup_iL_i$ satisfies $|N(D)|\le d$ and $w(D)\le c$.
--
--   The module also fixes "maximum degree at most $\delta$", **C4-free** (no hole of length four) and **prism-free** (no induced prism, in the sense of the published `StrongPerfectGraph.OddPrism.IsPrism`). These are the objects in which every statement of the mission is written.
--
--   **Formalization Note** Vertex sets are `Finset`s; distances are walk lengths inside $U$, never `SimpleGraph.dist`, which is $0$ between components. Induced paths and holes are the published `StrongPerfectGraph.OddPrism.IsInducedPath` and `IsHole`.
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, §1, pp.2–4 (weights, uniform weights, balanced separators, paths, N^d[v], d-bounded, even pairs and sets, iterated even sets, even set separators, N(X), N[X]); prism p.2

import Mathlib
import Definitions.Def_StrongPerfectGraph_OddPrism_IsBerge
import Definitions.Def_StrongPerfectGraph_OddPrism_IsPrism

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace SubmodPerfect

/-! # Graphs, induced paths, weights, balanced separators and even set separators

Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*,
arXiv:2110.00108v2, §1, pp.1–4.

**Formalization Note.** Graphs are `G : SimpleGraph V` on a finite type `V`. An induced
subgraph `G[U]` of the paper is represented by its vertex set `U : Finset V`; every notion
below that the paper uses inside an induced subgraph takes the ambient vertex set `U` as an
argument, and `U = Finset.univ` is `G` itself. A *path* is always an **induced** path (p.2),
written as a list with the published `StrongPerfectGraph.OddPrism.IsInducedPath`; its length is
`p.length - 1`. Decidability is classical throughout. -/

variable {V : Type*} [Fintype V]

/-- `N(X)` in `G` (p.4): the vertices outside `X` with a neighbour in `X`. -/
def nbhd (G : SimpleGraph V) (X : Finset V) : Finset V :=
  Finset.univ.filter (fun v => v ∉ X ∧ ∃ x ∈ X, G.Adj x v)

/-- `N[X] = N(X) ∪ X` in `G` (p.4). -/
def closedNbhd (G : SimpleGraph V) (X : Finset V) : Finset V :=
  X ∪ nbhd G X

/-- `N(X)` taken in the induced subgraph `G[U]`. -/
def nbhdIn (G : SimpleGraph V) (U X : Finset V) : Finset V :=
  nbhd G X ∩ U

/-- `N[X]` taken in the induced subgraph `G[U]`. -/
def closedNbhdIn (G : SimpleGraph V) (U X : Finset V) : Finset V :=
  X ∪ nbhdIn G U X

/-- `D` is a connected component of the induced subgraph `G[U]`: a nonempty subset of `U`
inducing a connected graph, with no edge from `D` to `U \ D` (so it is maximal). -/
def IsComponentIn (G : SimpleGraph V) (U D : Finset V) : Prop :=
  D ⊆ U ∧ D.Nonempty ∧ (G.induce (D : Set V)).Connected ∧
    ∀ x ∈ D, ∀ y ∈ U, G.Adj x y → y ∈ D

/-- `N^d[v]` in `G[U]` (p.3): the vertices of `U` at distance at most `d` from `v` in `G[U]`,
i.e. reachable from `v` by a walk of length at most `d` all of whose vertices lie in `U`.

**Formalization Note.** Distances are walk lengths, not `SimpleGraph.dist` (which is `0`
between different components). The ball is empty when `v ∉ U`. -/
def ball (G : SimpleGraph V) (U : Finset V) (v : V) (d : ℕ) : Finset V :=
  U.filter (fun u => ∃ p : G.Walk v u, p.length ≤ d ∧ ∀ z ∈ p.support, z ∈ U)

/-- `X` is `d`-bounded in `G[U]` (p.3): `X ⊆ N^d[v]` for some vertex `v` of `G[U]`. -/
def IsBoundedIn (G : SimpleGraph V) (U : Finset V) (d : ℕ) (X : Finset V) : Prop :=
  ∃ v ∈ U, X ⊆ ball G U v d

/-- `G` has maximum degree at most `δ`. -/
def MaxDegreeLe (G : SimpleGraph V) (δ : ℕ) : Prop :=
  ∀ v, (Finset.univ.filter (fun u => G.Adj v u)).card ≤ δ

/-- `G` is `C4`-free: no hole of length four (an induced four-cycle). -/
def IsC4Free (G : SimpleGraph V) : Prop :=
  ¬ ∃ c : List V, StrongPerfectGraph.OddPrism.IsHole G c ∧ c.length = 4

/-- `G` is prism-free (p.2): no induced prism. A prism is given by its three paths, as in the
published `StrongPerfectGraph.OddPrism.IsPrism`. -/
def IsPrismFree (G : SimpleGraph V) : Prop :=
  ¬ ∃ p₁ p₂ p₃ : List V, StrongPerfectGraph.OddPrism.IsPrism G p₁ p₂ p₃

/-- `p` is a path of `G` from `x` to `y` (p.2): an induced path listed from `x` to `y`. -/
def IsPathFrom (G : SimpleGraph V) (p : List V) (x y : V) : Prop :=
  StrongPerfectGraph.OddPrism.IsInducedPath G p ∧ p.head? = some x ∧ p.getLast? = some y

/-- `{x, y}` is an even pair of `G[U]` (p.3): `x ≠ y` are vertices of `U` and every induced path
of `G[U]` from `x` to `y` has even length. (An induced path of `G[U]` is an induced path of `G`
with all vertices in `U`.) -/
def IsEvenPairIn (G : SimpleGraph V) (U : Finset V) (x y : V) : Prop :=
  x ≠ y ∧ x ∈ U ∧ y ∈ U ∧
    ∀ p : List V, IsPathFrom G p x y → (∀ z ∈ p, z ∈ U) → Even (p.length - 1)

/-- `X` is an even set of `G[U]` (p.3): `X ⊆ U` and every two distinct vertices of `X` form an
even pair of `G[U]`. -/
def IsEvenSetIn (G : SimpleGraph V) (U X : Finset V) : Prop :=
  X ⊆ U ∧ ∀ x ∈ X, ∀ y ∈ X, x ≠ y → IsEvenPairIn G U x y

/-- `(L 0, …, L (k-1))` is a `k`-iterated even set of `G[U]` (p.3): the sets are pairwise
disjoint subsets of `U`, and `L i` is an even set of `G[U] \ ⋃_{j<i} L j`. Empty entries are
allowed. -/
def IsIteratedEvenSetIn (G : SimpleGraph V) (U : Finset V) {k : ℕ} (L : Fin k → Finset V) :
    Prop :=
  (∀ i j, i ≠ j → Disjoint (L i) (L j)) ∧
    ∀ i, L i ⊆ U ∧
      IsEvenSetIn G (U \ (Finset.univ.filter (fun j => j < i)).biUnion L) (L i)

/-- `w(X) = ∑_{x ∈ X} w(x)` (p.2). -/
def wsum (w : V → ℝ) (X : Finset V) : ℝ :=
  ∑ x ∈ X, w x

/-- `w` is a weight function on `G[U]` (p.2): `w(v) ∈ [0, 1]` for every vertex `v` of `U`. -/
def IsWeightFunctionOn (w : V → ℝ) (U : Finset V) : Prop :=
  ∀ v ∈ U, 0 ≤ w v ∧ w v ≤ 1

/-- The uniform weight function of a set `X` (p.2): `1/|X|` on `X` and `0` elsewhere. It is
used only for nonempty `X`. -/
def uniformWeight (X : Finset V) (v : V) : ℝ :=
  if v ∈ X then 1 / (X.card : ℝ) else 0

/-- `X` is a `(w, c)`-balanced separator of `G[U]` (p.2): `X ⊆ U` and every connected
component `D` of `G[U] \ X` has `w(D) ≤ c`. -/
def IsBalancedSepIn (G : SimpleGraph V) (U : Finset V) (w : V → ℝ) (c : ℝ) (X : Finset V) :
    Prop :=
  X ⊆ U ∧ ∀ D, IsComponentIn G (U \ X) D → wsum w D ≤ c

/-- `G[U]` has a `d`-bounded `(w, c)`-balanced separator (p.3). -/
def HasBoundedBalancedSepIn (G : SimpleGraph V) (U : Finset V) (w : V → ℝ) (c : ℝ) (d : ℕ) :
    Prop :=
  ∃ X, IsBoundedIn G U d X ∧ IsBalancedSepIn G U w c X

/-- `L = (L 0, …, L (k-1))` is a `(w, k, c, d)`-even set separator of `G` (p.3): `L` is a
`k`-iterated even set of `G`, and every connected component `D` of `G \ (⋃ L i)` satisfies
`|N(D)| ≤ d` and `w(D) ≤ c`, with `N(D)` taken in `G`. -/
def IsEvenSetSeparator (G : SimpleGraph V) (w : V → ℝ) (k : ℕ) (c : ℝ) (d : ℕ)
    (L : Fin k → Finset V) : Prop :=
  IsIteratedEvenSetIn G Finset.univ L ∧
    ∀ D, IsComponentIn G (Finset.univ \ Finset.univ.biUnion L) D →
      (nbhd G D).card ≤ d ∧ wsum w D ≤ c

end SubmodPerfect


