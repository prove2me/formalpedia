-- Prove2me | Definitions.Def_SNPTreedepth_treedepth
-- name    : SNPTreedepth_treedepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:08.279208+00:00
-- url     : https://prove2.me/theorems/0130f69a-0d5e-4c09-b748-32cb10ee6324
-- title:
--   Rooted forests, closure, height, treedepth and treedepth decompositions
-- statement:
--   A **rooted forest** $F$ is a disjoint union of rooted trees; the **depth** of a vertex is the number of vertices on the path from its root to it, and the **height** of $F$ is the maximum depth. A vertex $x$ is an **ancestor** of $y$ if it lies on the root path of $y$ (every vertex is an ancestor of itself). The **closure** $\mathrm{clos}(F)$ joins $x\ne y$ whenever one is an ancestor of the other. The **treedepth** of a graph $G$ is
--   $$
--   \mathrm{td}(G)=\min\{\mathrm{height}(F) : G\subseteq \mathrm{clos}(F)\},
--   $$
--   and a **treedepth decomposition** of $G$ is a rooted *tree* $T$ on the vertices of $G$ with $G\subseteq\mathrm{clos}(T)$ (this can cost one level compared with elimination forests). For a relational structure, $\mathrm{td}(R)$ and its treedepth decompositions are those of its Gaifman graph.
--
--   The parameter of the whole mission is $\mathrm{td}(R)+|\varphi|$.
--
--   **Formalization Note** A forest is given by a parent function together with its depth function (roots have depth $1$, a child one more than its parent), which rules out cycles. Decompositions use no vertices beyond the elements. The module also provides the children of a vertex and the root path $(w_1,\dots,w_d)$ of a vertex.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), §3 Treedepth, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure

set_option autoImplicit false

namespace SNPTreedepth

/-- A **rooted forest** on the vertex set `V` (Depian et al., *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), Treedepth,
p.16): "a disjoint union of rooted trees". The depth of `x` is "the number of vertices on the path
from the root of T to x".

**Formalization Note** The forest is given by its parent function (`none` at a root). The field
`depth` is the depth of the paper (a root has depth `1`, a child one more than its parent); its two
equations force the parent relation to be acyclic, so `depth` is determined by `parent`. The
forest has no vertices beyond `V` (p.16: "a treedepth decomposition of a relational structure
contains no vertices beyond the elements of that structure"). -/
structure RootedForest (V : Type*) where
  /-- the parent of a vertex, `none` at a root -/
  parent : V → Option V
  /-- the depth of a vertex: the number of vertices on its root path -/
  depth : V → ℕ
  depth_root : ∀ v, parent v = none → depth v = 1
  depth_parent : ∀ v w, parent v = some w → depth v = depth w + 1

namespace RootedForest

variable {V : Type*}

/-- `x` is an **ancestor** of `y`: `x` lies on the path from the root to `y`.

**Formalization Note** The relation is reflexive, as in Lemma 18 (3), p.17, and Lemma 22 (1),
p.22: "we call a vertex an ancestor of itself". -/
def IsAncestor (F : RootedForest V) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => F.parent b = some a) x y

/-- The **closure** `clos(F)` (Depian et al., p.16): the graph on `V` with an edge `xy` whenever
`x ≠ y` and `x` is an ancestor of `y`. -/
def closure (F : RootedForest V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (F.IsAncestor x y ∨ F.IsAncestor y x)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The **height** of a rooted forest (Depian et al., p.16): the maximum depth of a vertex (`0`
for an empty vertex set). -/
def height [Fintype V] (F : RootedForest V) : ℕ :=
  Finset.univ.sup F.depth

/-- The forest is a **rooted tree**: it has exactly one root. -/
def IsTree (F : RootedForest V) : Prop :=
  ∃! v, F.parent v = none

/-- The children of `x`: the vertices whose parent is `x`. -/
noncomputable def children [Fintype V] (F : RootedForest V) (x : V) : Finset V :=
  open Classical in Finset.univ.filter (fun c => F.parent c = some x)

/-- The root path `(w₁, …, w_d)` of `v`, from the root `w₁` to `w_d = v`, where `d` is the depth of
`v` (Depian et al., Definition 2, p.17). Computed by following parents `depth v` times. -/
def rootPathAux (F : RootedForest V) : ℕ → V → List V
  | 0, v => [v]
  | n + 1, v =>
    match F.parent v with
    | none => [v]
    | some w => F.rootPathAux n w ++ [v]

/-- The root path `(w₁, …, w_d = v)` of `v` (Depian et al., Definition 2, p.17). -/
def rootPath (F : RootedForest V) (v : V) : List V :=
  F.rootPathAux (F.depth v - 1) v

end RootedForest

/-- The **treedepth** `td(G)` of a graph (Depian et al., p.16): "the minimum height of any rooted
forest F such that G ⊆ clos(F)".

**Formalization Note** `sInf` over `ℕ`; the set is nonempty (a path through all vertices is such a
forest), so this is a minimum. -/
noncomputable def treedepth {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {h : ℕ | ∃ F : RootedForest V, G ≤ F.closure ∧ F.height ≤ h}

/-- A **treedepth decomposition** of a graph `G` (Depian et al., p.16): "a rooted tree T such that
G ⊆ clos(T)", with no vertices beyond those of `G`. (Footnote 9: this can add `1` to the height
compared to elimination forests.) -/
def IsTDDecompGraph {V : Type*} (G : SimpleGraph V) (T : RootedForest V) : Prop :=
  T.IsTree ∧ G ≤ T.closure

/-- The **treedepth** `td(R)` of a relational structure: the treedepth of its Gaifman graph
(Depian et al., p.16). -/
noncomputable def td {σ : Signature} {V : Type*} [Fintype V] (R : Structure σ V) : ℕ :=
  treedepth R.gaifman

/-- A **treedepth decomposition of a relational structure** (Depian et al., p.16): a treedepth
decomposition of its Gaifman graph, on exactly the elements of the structure. -/
def IsTDDecomp {σ : Signature} {V : Type*} (R : Structure σ V) (T : RootedForest V) : Prop :=
  IsTDDecompGraph R.gaifman T

end SNPTreedepth


