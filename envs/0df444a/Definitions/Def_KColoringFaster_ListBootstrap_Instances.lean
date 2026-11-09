-- Prove2me | Definitions.Def_KColoringFaster_ListBootstrap_Instances
-- name    : KColoringFaster_ListBootstrap_Instances
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:08.480646+00:00
-- url     : https://prove2.me/theorems/7aab0377-ad2d-4948-bb20-c01a6a691868
-- title:
--   §3.1, §3.2, Definition 3.4, §4.1 — graph and list-coloring instances, encodings, (α, Δ)-bounded graphs, bad active vertices
-- statement:
--   This definition fixes the objects every statement of the mission is about.
--
--   A **graph instance** is a simple graph $G$ on the vertex set $\{0,\dots,n-1\}$. It is **$k$-colorable** if there is a map $c:V(G)\to[k]$ with $c(u)\neq c(v)$ for every edge $uv$ (§3.1, p. 7).
--
--   A **list-coloring instance** $(G,L)$ is a simple graph $G$ on $\{0,\dots,n-1\}$ together with a finite list $L(v)\subseteq\mathbb N$ of colors at each vertex. A **list coloring** is a map $c:V(G)\to\mathbb N$ with $c(v)\in L(v)$ for every vertex and $c(u)\neq c(v)$ on every edge. The instance belongs to **$k$-list-coloring** if $|L(v)|\le k$ for every $v$. The **singleton restriction** of $(G,L)$ at $v$ to a color $c$ replaces $L(v)$ by $\{c\}$ and changes nothing else (§3.2, p. 8).
--
--   A graph is **$(\alpha,\Delta)$-bounded** if at least $\alpha\,|V(G)|$ of its vertices have degree at most $\Delta$ (Definition 3.4, p. 9).
--
--   In a $k$-list-coloring instance a vertex is **active** if $|L(v)|=k$. Relative to a list coloring $w$ and a threshold $\Delta_1$, an active vertex $v$ is **good** if some color of $L(v)$ occurs on more than $\Delta_1$ neighbours of $v$ in $w$, and **bad** otherwise (§4.1, p. 12); $\mathrm{bad}(w)$ is the number of bad active vertices.
--
--   Algorithms receive instances as lists of integers. A graph is encoded as $n$ followed by the $n^2$ adjacency bits row by row; a list instance additionally lists, for each vertex in order, $|L(v)|$ followed by the elements of $L(v)$ in increasing order. A coloring is output as the list $c(0),\dots,c(n-1)$.
--
--   **Formalization Note** Colors are natural numbers, so the palette is unbounded; a list instance over a finite palette $P$ is obtained by numbering $P$. Lists may be empty, which the source excludes; an instance with an empty list has no list coloring. The encoding contains the instance and nothing else.
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 7, §3.1; p. 8, §3.2; p. 9, Definition 3.4; p. 12, §4.1

import Mathlib

open Classical

namespace KColoringFaster.ListBootstrap

/-! # Graph and list-coloring instances, and their canonical encodings

Zamir, *k-Coloring is Faster than Computing the Chromatic Number*, arXiv:2607.25973 (revision of
9 Sep 2026), §3.1, p. 7, and §3.2, p. 8.

**Formalization Note.**
* Vertices are `Fin n`. Colors are natural numbers, so the palette is unbounded: a list-coloring
  instance over any finite palette `P` is the instance obtained by numbering `P`.
* Lists are finite sets of colors. They may be empty (the source requires them nonempty); an
  instance with an empty list has no list coloring.
* The encodings are the inputs of the algorithms of this mission: `n`, then the `n²` adjacency bits
  row by row (`1` for an edge, `0` otherwise), then, for a list instance, for each vertex in order the
  size of its list followed by its colors in increasing order. They contain the instance and nothing
  else. -/

/-- A graph on the vertex set `Fin n`: the input of the k-coloring problem (§3.1, p. 7). -/
structure GraphInstance where
  n : ℕ
  G : SimpleGraph (Fin n)

/-- §3.1, p. 7: `G` is **k-colorable** if there is a map `c : V(G) → [k]` with `c u ≠ c v` on every
edge. (This is Mathlib's `G.Colorable k`.) -/
def GraphInstance.KColorable (k : ℕ) (g : GraphInstance) : Prop :=
  ∃ c : Fin g.n → Fin k, ∀ u v, g.G.Adj u v → c u ≠ c v

/-- A list-coloring instance (§3.1, p. 7): a graph on `Fin n` with a finite list of natural-number
colors at each vertex. -/
structure ListInstance where
  n : ℕ
  G : SimpleGraph (Fin n)
  L : Fin n → Finset ℕ

/-- `c` is a list coloring of the graph `G` with lists `L`: `c v ∈ L v` for every vertex and
`c u ≠ c v` on every edge (§3.1, p. 7). -/
def IsListColoringOf {n : ℕ} (G : SimpleGraph (Fin n)) (L : Fin n → Finset ℕ)
    (c : Fin n → ℕ) : Prop :=
  (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- A list coloring of the instance `I`. -/
def IsListColoring (I : ListInstance) (c : Fin I.n → ℕ) : Prop :=
  IsListColoringOf I.G I.L c

/-- The instance `I` has a list coloring. -/
def ListColorable (I : ListInstance) : Prop :=
  ∃ c : Fin I.n → ℕ, IsListColoring I c

/-- All lists have size at most `k`: the instance belongs to k-list-coloring (§3.1, p. 7). -/
def MaxListLE (k : ℕ) (I : ListInstance) : Prop :=
  ∀ v, (I.L v).card ≤ k

/-- Singleton restriction (§3.2, p. 8): replace the list of `v` by `{c}`. The graph is unchanged. -/
def restrictAt (I : ListInstance) (v : Fin I.n) (c : ℕ) : ListInstance where
  n := I.n
  G := I.G
  L := Function.update I.L v {c}

/-- The `n²` adjacency bits of `G`, row by row. -/
noncomputable def adjBits {n : ℕ} (G : SimpleGraph (Fin n)) : List ℤ :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => if G.Adj i j then 1 else 0

/-- A finite set of naturals: its size, then its elements in increasing order. -/
def encFinset (s : Finset ℕ) : List ℤ :=
  (s.card : ℤ) :: (s.sort (· ≤ ·)).map fun x => (x : ℤ)

/-- Canonical encoding of a graph: `n`, then the adjacency bits. -/
noncomputable def encGraph (g : GraphInstance) : List ℤ :=
  (g.n : ℤ) :: adjBits g.G

/-- Canonical encoding of a list instance: the graph, then each vertex's list in vertex order. -/
noncomputable def encList (I : ListInstance) : List ℤ :=
  ((I.n : ℤ) :: adjBits I.G) ++ (List.finRange I.n).flatMap fun v => encFinset (I.L v)

/-- Output encoding of a coloring: the colors `c 0, …, c (n-1)`. -/
def encColoring {n : ℕ} (c : Fin n → ℕ) : List ℤ :=
  (List.finRange n).map fun v => (c v : ℤ)

/-- An output word is (the encoding of) a list coloring of `I`. -/
def IsColoringOutput (I : ListInstance) (out : List ℤ) : Prop :=
  ∃ c : Fin I.n → ℕ, IsListColoring I c ∧ out = encColoring c

/-- Definition 3.4, p. 9: a graph is **(α, Δ)-bounded** if at least `α·|V(G)|` of its vertices have
degree at most `Δ`. -/
def IsBoundedGraph (α Δ : ℝ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  α * (n : ℝ) ≤ ((Finset.univ.filter fun v : Fin n => (G.degree v : ℝ) ≤ Δ).card : ℝ)

/-- §4.1, p. 12: a vertex is **active** in a k-list instance if its list has size exactly `k`. -/
def IsActive (k : ℕ) (I : ListInstance) (v : Fin I.n) : Prop :=
  (I.L v).card = k

/-- §4.1, p. 12: relative to a witness coloring `w`, an active vertex is **good** if some color of its
list occurs on more than `Δ₁` of its neighbours, and **bad** otherwise. -/
def IsBad (k Δ₁ : ℕ) (I : ListInstance) (w : Fin I.n → ℕ) (v : Fin I.n) : Prop :=
  IsActive k I v ∧
    ∀ col ∈ I.L v, (Finset.univ.filter fun u : Fin I.n => I.G.Adj v u ∧ w u = col).card ≤ Δ₁

/-- The number of bad active vertices relative to `w`. -/
noncomputable def badCount (k Δ₁ : ℕ) (I : ListInstance) (w : Fin I.n → ℕ) : ℕ :=
  (Finset.univ.filter fun v => IsBad k Δ₁ I w v).card

end KColoringFaster.ListBootstrap


