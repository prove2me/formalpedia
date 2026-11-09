-- Prove2me | Definitions.Def_WalkTreeCluster_Graph
-- name    : WalkTreeCluster_Graph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:39:15.702199+00:00
-- url     : https://prove2.me/theorems/33b13b0e-5657-4e0b-a192-362411b15f13
-- title:
--   Neighbor-list graphs, cluster families (Definition 1.2) and the lazy walk $M=\tfrac12(I+A/d)$
-- statement:
--   The graph $G=(V,E)$ has vertex set $V=\{0,\dots,n-1\}$ and is given by neighbor lists: every vertex $u$ has $d$ slots, and the neighbor query $(u,r)$, $r\in\{1,\dots,d\}$, returns the $r$-th neighbor of $u$. A self-loop occupies one slot and counts once towards the degree, so $G$ is $d$-regular. The adjacency matrix $A$ has entries $A(x,y)=\#\{r : \text{the } r\text{-th neighbor of } x \text{ is } y\}$; the graph is *undirected* when $A$ is symmetric, and has *no parallel edges* when $A(x,y)\le 1$ for $x\ne y$ (loops may repeat).
--
--   For disjoint $T,W\subseteq V$, $|E_G(T,W)|=\sum_{x\in T}\sum_{y\in W}A(x,y)$ is the number of edges joining them, and $|\partial_G C|=|E_G(C,V\setminus C)|$.
--
--   **Definition 1.2 (clusters plus noise).** Let $\epsilon>0$ and $0<\phi\le1$. A family $\mathcal C$ of disjoint nonempty vertex sets is a *family of clusters* if every $C\in\mathcal C$ satisfies
--   1. (internal expansion) $|E_G(T,C\setminus T)|\ge\phi\, d\,|T|$ for every $T\subseteq C$ with $0<|T|\le|C|/2$;
--   2. (sparse boundary) $|\partial_G C|\le\epsilon\, d\,|C|$.
--
--   Write $S=\bigcup_{C\in\mathcal C}C$, $\mathbb 1_u$ for the coordinate vector of $u$, $u_C=\mathbb 1_C/|C|$ for the mean of a cluster, and
--   $$M=\tfrac12\Big(I+\frac{A}{d}\Big)$$
--   for the lazy random-walk matrix (Eq. (21)).
--
--   These objects are the model of every statement of the mission.
--
--   **Formalization Note.** Definition 1.2 is used in its multiplied form ($|E_G(T,C\setminus T)|/(d|T|)\ge\phi$ becomes $\phi d|T|\le|E_G(T,C\setminus T)|$), equivalent because $d|T|>0$; $|C|/2$ is real division. The conditions $\epsilon>0$, $0<\phi\le1$ are hypotheses of the theorems.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Definition 1.2, p.2; Section 4 (graph notation, linear algebra notation, Eq. (21)), p.16

import Mathlib

open scoped Classical

namespace WalkTreeCluster

/-!
# Neighbor-list graphs, cluster families and the lazy walk

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Definition 1.2, p.2; Section 4 ("Graph notation", "Linear
algebra notation", "Graph access model", Eq. (21)), p.16.

The graph is given by neighbor lists: `nbr u r` is the `(r + 1)`-th neighbor of `u`, so the page's
neighbor query `(u, r)` with `r ∈ {1, …, d}` returns `nbr u (r − 1)`.

**Formalization Note.**
* The vertex set is `V = Fin n`. A graph is `nbr : Fin n → Fin d → Fin n`, `d` slots per vertex, so
  every vertex has degree exactly `d` (d-regular), with each self-loop occupying one slot (the page
  counts each self-loop once towards the degree). Loops may repeat (Remark 4.1 pads degrees with
  loops). The neighbor order is arbitrary.
* `adj nbr x y` is the number of slots of `x` pointing to `y`: the entry `A(x, y)` of the adjacency
  matrix. `IsUndirected` says `A` is symmetric; `NoParallel` says there is at most one edge between
  two distinct vertices.
* For disjoint `T, W`, `edgeCount nbr T W` is the number of edges joining them, `|E_G(T, W)|`;
  `boundary nbr C = |∂_G C| = |E_G(C, V ∖ C)|`.
* Definition 1.2 is used in its multiplied form: `|E_G(T, C∖T)| / (d|T|) ≥ ϕ` is written
  `ϕ·d·|T| ≤ |E_G(T, C∖T)|` and `|∂_G C| / (d|C|) ≤ ϵ` is `|∂_G C| ≤ ϵ·d·|C|`; the two forms agree
  since `d|T| > 0` and `d|C| > 0` (for `d ≥ 1`). `|C|/2` is real division. The conditions
  `ϵ > 0`, `0 < ϕ ≤ 1` are hypotheses of the theorems, not part of the predicate.
-/

/-- `A(x, y)`: the number of neighbor slots of `x` that point to `y` (Section 4, p.16). A self-loop
at `x` counts once per slot. -/
def adj {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (x y : Fin n) : ℕ :=
  (Finset.univ.filter (fun r : Fin d => nbr x r = y)).card

/-- The graph is undirected: the adjacency matrix is symmetric. -/
def IsUndirected {n d : ℕ} (nbr : Fin n → Fin d → Fin n) : Prop :=
  ∀ x y : Fin n, adj nbr x y = adj nbr y x

/-- No parallel non-loop edges: two distinct vertices are joined by at most one edge. Self-loops may
repeat. -/
def NoParallel {n d : ℕ} (nbr : Fin n → Fin d → Fin n) : Prop :=
  ∀ x y : Fin n, x ≠ y → adj nbr x y ≤ 1

/-- `|E_G(T, W)|`: for disjoint `T, W`, the number of edges joining `T` to `W`. -/
def edgeCount {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (T W : Finset (Fin n)) : ℕ :=
  ∑ x ∈ T, ∑ y ∈ W, adj nbr x y

/-- `|∂_G C| = |E_G(C, V ∖ C)|`. -/
def boundary {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (C : Finset (Fin n)) : ℕ :=
  edgeCount nbr C Cᶜ

/-- Definition 1.2 (Clusters plus noise), p.2: `𝒞` is a family of disjoint nonempty vertex sets, each
of which (1) induces a `ϕ`-expander, `|E_G(T, C∖T)| ≥ ϕ d |T|` for every `T ⊆ C` with
`0 < |T| ≤ |C|/2`, and (2) has a sparse boundary, `|∂_G C| ≤ ϵ d |C|`. -/
def IsClusterFamily {n d : ℕ} (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ)
    (𝒞 : Finset (Finset (Fin n))) : Prop :=
  (𝒞 : Set (Finset (Fin n))).PairwiseDisjoint id ∧
  (∀ C ∈ 𝒞, C.Nonempty) ∧
  ∀ C ∈ 𝒞,
    (∀ T ⊆ C, 0 < T.card → (T.card : ℝ) ≤ (C.card : ℝ) / 2 →
      ϕ * d * T.card ≤ (edgeCount nbr T (C \ T) : ℝ)) ∧
    (boundary nbr C : ℝ) ≤ ϵ * d * C.card

/-- `S = ⋃_{C ∈ 𝒞} C`, the union of the clusters. -/
def clusterUnion {n : ℕ} (𝒞 : Finset (Finset (Fin n))) : Finset (Fin n) :=
  𝒞.biUnion id

/-- The coordinate vector `1_u ∈ ℝ^V` (Section 4, p.16). -/
noncomputable def coord {n : ℕ} (u : Fin n) : Fin n → ℝ :=
  Pi.single u 1

/-- The cluster mean `u_C = 1_C / |C|` (Section 4, p.16). -/
noncomputable def clusterMean {n : ℕ} (C : Finset (Fin n)) : Fin n → ℝ :=
  fun z => if z ∈ C then 1 / (C.card : ℝ) else 0

/-- The lazy random-walk matrix `M = (I + A/d)/2`, Eq. (21), p.16. -/
noncomputable def walkMatrix {n d : ℕ} (nbr : Fin n → Fin d → Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (1 + (1 / (d : ℝ)) • Matrix.of (fun x y => (adj nbr x y : ℝ)))

end WalkTreeCluster


