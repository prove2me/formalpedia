-- Prove2me | Definitions.Def_EuclidKSteiner_MergeTree
-- name    : EuclidKSteiner_MergeTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:36.834511+00:00
-- url     : https://prove2.me/theorems/dc6e8feb-f724-43cb-9504-abf32dea5408
-- title:
--   The merge tree $\mathrm{Merge}_M$, path-union lengths and the colorings $\chi_x$
-- statement:
--   Let $M$ be a tree on $P$ with nonnegative weights.
--
--   1. **Merge tree.** Its vertices are **clusters**: the leaves $\{v\}$ ($v\in P$) and the vertex sets of the components of $M_{\le t}$ for each edge weight $t$ of $M$. The root $\rho$ is the cluster $P$. The **height** $h(C)$ is $0$ for a singleton and otherwise the largest weight of an edge of $M$ inside $C$. The parent of $C\ne P$ is the smallest cluster strictly containing $C$, and the edge into $C$ has length $h(\mathrm{parent}(C))-h(C)$.
--   2. **Path unions.** $\mathrm{Merge}_M(X)$ is the union of the paths from $\rho$ to the leaves in $X$, and $\mathrm{len}(\mathrm{Merge}_M(X))$ is its total length, each edge counted once.
--   3. **Colorings.** For a red–blue coloring $\chi$ of the merge-tree edges, $\mathrm{red}_\chi(X)$ and $\mathrm{blue}_\chi(X)$ are the total lengths of the red and of the blue edges of $\mathrm{Merge}_M(X)$; $\chi$ **separates** disjoint $A,B$ if $\mathrm{Merge}_M(A)\setminus\mathrm{Merge}_M(B)$ is red and $\mathrm{Merge}_M(B)\setminus\mathrm{Merge}_M(A)$ is blue.
--   4. **String colorings.** Each internal vertex chooses a **heavy** child with the largest number of leaves; the other child edges are **light**, and the light edges are numbered by distinct positions in $\{1,\dots,n-1\}$, $n=|P|$. A string $x$ gives the root the stored color $c(\rho)=x_0$; a heavy edge copies the parent's color and a light edge with number $j$ adds $x_j$ mod 2. The coloring $\chi_x$ gives each edge the stored color of its child.
--
--   **Formalization Note** Merge-tree vertices are identified with their clusters and edges with their child clusters, as on the page; $\mathrm{Merge}_M(X)$ consists of the clusters $C\ne P$ meeting $X$. Red is $0$ (`false`), blue is $1$ (`true`).
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), §3.4, p.13 (PDF p.15); §5.1, pp.20–21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_EuclidKSteiner_TermTree

namespace EuclidKSteiner

open Classical

/-!
# The merge tree `Merge_M`, path-union lengths, red–blue colorings and the string colorings `χ_x`

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), §3.4, p.13 (PDF p.15); §5.1, pp.20–21
(PDF pp.22–23).

**Formalization Note**
* A merge-tree vertex is identified with its **cluster** (its set of descendant leaves), as the page
  does ("A vertex can be identified with its set C ⊆ P of descendant leaves, called its cluster").
  The clusters are the singletons `{v}`, `v ∈ P` (the leaves), and the vertex sets of the components
  of `M_{≤t}` for `t` an edge weight of `M` (the components newly formed at that threshold, or
  carried over unchanged, which are the same vertex). The root `ρ` is the cluster `P`.
* `h(C)` is `0` for a singleton and otherwise the largest weight of an edge of `M` inside `C`, the
  threshold at which the component `C` is formed.
* The parent of a cluster `C ≠ P` is the smallest cluster strictly containing it (clusters are
  laminar, so the clusters containing `C` form a chain). Merge-tree edges are named by their child
  cluster; the edge into `C` has length `h(parent C) − h(C)`.
* `Merge_M(X)` is the set of edges `C ≠ P` with `C ∩ X ≠ ∅` (an edge lies on a path from `ρ` to a
  leaf of `X` exactly when its child cluster contains a leaf of `X`); for `X = ∅` it is empty.
* A red–blue coloring is a map from clusters (edges) to `Bool`, `false` = red (`0`),
  `true` = blue (`1`).
-/

variable {V : Type*} [DecidableEq V]

namespace TermTree

variable (T : TermTree V)

/-- The edges of `M` of weight at most `t`, i.e. `M_{≤t}`. -/
noncomputable def threshold (t : ℝ) : Finset (Sym2 V) := T.M.filter (fun e => T.w e ≤ t)

/-- The vertex set of the component of `v` in `M_{≤t}` (within `P`). -/
noncomputable def compAt (t : ℝ) (v : V) : Finset V :=
  T.P.filter fun u =>
    (SimpleGraph.fromEdgeSet ((T.threshold t : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v

/-- The **clusters** of `Merge_M`: the leaves `{v}`, `v ∈ P`, and the components of `M_{≤t}` for
every edge weight `t` of `M`. Source: §3.4, p.13 (PDF p.15). -/
noncomputable def clusters : Finset (Finset V) :=
  T.P.image (fun v => {v}) ∪ (T.M.image T.w).biUnion (fun t => T.P.image (T.compAt t))

/-- The **height** `h(C)`: `0` for a singleton, otherwise the largest weight of an edge of `M`
inside `C`. Source: §3.4, p.13 (PDF p.15): "its height is the weight at which that merge occurs …
with singleton heights zero". -/
noncomputable def height (C : Finset V) : ℝ :=
  if C.card ≤ 1 then 0 else
  if h : (T.M.filter (fun e => ∀ v ∈ e, v ∈ C)).Nonempty then
    (T.M.filter (fun e => ∀ v ∈ e, v ∈ C)).sup' h T.w
  else 0

/-- The clusters strictly containing `C`. -/
noncomputable def strictSupers (C : Finset V) : Finset (Finset V) :=
  T.clusters.filter (fun D => C ⊂ D)

/-- The **parent** of a cluster `C ≠ P`: the smallest cluster strictly containing `C` (unique by
laminarity); `C` itself if there is none. -/
noncomputable def parent (C : Finset V) : Finset V :=
  if h : (T.strictSupers C).Nonempty then
    Classical.choose (Finset.exists_min_image (T.strictSupers C) Finset.card h)
  else C

/-- The **length** of the merge-tree edge into `C`: its parent's height minus its own height. -/
noncomputable def edgeLen (C : Finset V) : ℝ := T.height (T.parent C) - T.height C

/-- The edges of **`Merge_M(X)`**, the union of the paths from `ρ` to the leaves in `X`, each named
by its child cluster. Source: §3.4, p.13 (PDF p.15). -/
noncomputable def mergeEdges (X : Finset V) : Finset (Finset V) :=
  T.clusters.filter (fun C => C ≠ T.P ∧ (C ∩ X).Nonempty)

/-- **`len(Merge_M(X))`**: the total length of the edges of `Merge_M(X)`, each counted once.
Source: §3.4, p.13 (PDF p.15). -/
noncomputable def lenMerge (X : Finset V) : ℝ := ∑ C ∈ T.mergeEdges X, T.edgeLen C

/-- The height `h(ρ)` of the root (cluster `P`). -/
noncomputable def rootHeight : ℝ := T.height T.P

/-- `red_χ(X)`: the total length of the red edges of `Merge_M(X)` (`false` = red).
Source: §5.1, p.20 (PDF p.22). -/
noncomputable def redLen (χ : Finset V → Bool) (X : Finset V) : ℝ :=
  ∑ C ∈ (T.mergeEdges X).filter (fun C => χ C = false), T.edgeLen C

/-- `blue_χ(X)`: the total length of the blue edges of `Merge_M(X)` (`true` = blue).
Source: §5.1, p.20 (PDF p.22). -/
noncomputable def blueLen (χ : Finset V → Bool) (X : Finset V) : ℝ :=
  ∑ C ∈ (T.mergeEdges X).filter (fun C => χ C = true), T.edgeLen C

/-- The coloring `χ` **separates** the disjoint leaf sets `A, B`: `Merge_M(A) \ Merge_M(B)` is red and
`Merge_M(B) \ Merge_M(A)` is blue. Source: §5.1, p.20 (PDF p.22). -/
def Separates (χ : Finset V → Bool) (A B : Finset V) : Prop :=
  (∀ C ∈ T.mergeEdges A, C ∉ T.mergeEdges B → χ C = false) ∧
    (∀ C ∈ T.mergeEdges B, C ∉ T.mergeEdges A → χ C = true)

/-- The children of the merge-tree vertex `D`: the clusters `C ≠ P` whose parent is `D`. -/
noncomputable def childClusters (D : Finset V) : Finset (Finset V) :=
  T.clusters.filter (fun C => C ≠ T.P ∧ T.parent C = D)

/-- A **heavy-child choice**: every internal vertex `D` (a cluster with at least two leaves) picks a
child with the largest number of descendant leaves (ties broken arbitrarily). Its edge is heavy.
Source: §5.1.1, p.20 (PDF p.22): "Order the children of each internal vertex … by decreasing number
of descendant leaves, breaking ties arbitrarily. Call the edge to the leftmost child heavy and all
other child edges light". -/
def IsHeavyChoice (hv : Finset V → Finset V) : Prop :=
  ∀ D ∈ T.clusters, 2 ≤ D.card →
    hv D ∈ T.childClusters D ∧ ∀ C ∈ T.childClusters D, C.card ≤ (hv D).card

/-- The merge-tree edge into `C` is **light** for the heavy-child choice `hv`. -/
def IsLight (hv : Finset V → Finset V) (C : Finset V) : Prop :=
  C ∈ T.clusters ∧ C ≠ T.P ∧ hv (T.parent C) ≠ C

/-- A **numbering of the light edges** by distinct positions in `{1, …, n − 1}`, `n = |P|`.
Source: §5.1.1, p.21 (PDF p.23): "Number the light edges 1, …, n − 1 in their traversal order." -/
def IsLightNumbering (hv : Finset V → Finset V) (num : Finset V → ℕ) : Prop :=
  (∀ C, T.IsLight hv C → 1 ≤ num C ∧ num C ≤ T.P.card - 1) ∧
    ∀ C C', T.IsLight hv C → T.IsLight hv C' → num C = num C' → C = C'

/-- The **stored vertex color** `c(C)` produced by the string `x` (`false` = red = `0`,
`true` = blue = `1`): `c(ρ) = x_0`, a heavy edge copies the parent's color and the light edge into
`C` adds the bit `x_{num C}` mod 2. Equivalently `c(C) = x_0 + Σ x_{num D}` (mod 2) over the light
edges `D` on the path from `ρ` to `C`. Source: §5.1.1, p.21 (PDF p.23), steps 1–2. -/
noncomputable def storedColor (hv : Finset V → Finset V) (num : Finset V → ℕ) (x : ℕ → Bool)
    (C : Finset V) : Bool :=
  Bool.xor (x 0)
    (decide (Odd ((T.clusters.filter
      (fun D => C ⊆ D ∧ T.IsLight hv D ∧ x (num D) = true)).card)))

/-- The **string coloring `χ_x`**: each edge gets the stored color of its child endpoint.
Source: §5.1.1, p.21 (PDF p.23): "Give the edge uv color c(v)." -/
noncomputable def chi (hv : Finset V → Finset V) (num : Finset V → ℕ) (x : ℕ → Bool) :
    Finset V → Bool :=
  T.storedColor hv num x

end TermTree

end EuclidKSteiner


