-- Prove2me | Definitions.Def_KleeWalkup67_FiveStep_Polyhedra
-- name    : KleeWalkup67_FiveStep_Polyhedra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:41:44.281994+00:00
-- url     : https://prove2.me/theorems/98fb20e7-23be-4434-aa6f-bbafa1b5509c
-- title:
--   §1, p. 63, p. 69 — d-polyhedra with n facets, simple, faces and their dimension, (k₁, …, k_r)-paths, Dantzig figures, property A
-- statement:
--   This file fixes the objects of Klee and Walkup's paper, §§1–4. Throughout, $a_1,\dots,a_n\in\mathbb R^d$ and $b\in\mathbb R^n$, and
--   $$P=\{x\in\mathbb R^d : \langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}.$$
--   The **vertices** of $P$ are its extreme points, and two vertices $u\ne v$ are joined by an **edge** when the segment $[u,v]$ is an extreme subset of $P$. A **path of length $l$** from $x$ to $y$ is a sequence of $l$ edges $[x_0,x_1],\dots,[x_{l-1},x_l]$ with $x_0=x$, $x_l=y$; the distance $\delta_P(x,y)$ is the least such $l$.
--
--   1. **$d$-polyhedron with $n$ facets.** The paper's polyhedra are nonempty intersections of finitely many closed halfspaces (p. 55). The system $(a,b)$ is a *facet presentation* when $P$ has nonempty interior in $\mathbb R^d$ (so $P$ is $d$-dimensional) and no row is redundant: for each $i$ some point satisfies all inequalities except the $i$-th and violates the $i$-th. The $n$ rows are then in bijection with the $n$ facets of $P$, and row $i$ is tight at a point exactly when the point lies on the $i$-th facet.
--   2. **Tight set and simplicity.** $T(v)=\{i:\langle a_i,v\rangle=b_i\}$ is the set of facets incident to $v$ (the paper's $v$-facets, p. 57). $P$ is **simple** when it is pointed (has a vertex) and every vertex lies on exactly $d$ facets.
--   3. **Faces and dimension.** Besides $P$ itself, the faces of $P$ are its intersections with supporting hyperplanes; $\emptyset$ is not a face (p. 55). Here a face is a nonempty set $\{x\in P:\langle a_i,x\rangle=b_i\ \forall i\in I\}$ for a set of rows $I$ ($I=\emptyset$ gives $P$). The dimension of a set is the dimension of its affine hull.
--   4. **Facial paths** (p. 57). A $(k_1,\dots,k_r)$-path from $x$ to $y$, $r\ge1$, is a sequence $(K_1,\dots,K_r)$ of faces of $P$ with
--   $$x\in K_1,\quad y\in K_r,\quad \dim K_i=k_i\ (1\le i\le r),\quad K_i\cap K_{i+1}\ne\emptyset\ (1\le i<r).$$
--   A variant also requires that no $K_i$ lies entirely within a given set $F$ (used with a facet $F$ in 3.1).
--   5. **Dantzig figure** (p. 63). A triple $(P,x,y)$ is a $d$-dimensional Dantzig figure if $P$ is a $d$-polyhedron with $2d$ facets, $x,y$ are vertices, exactly $d$ facets are incident to $x$ and exactly $d$ others are incident to $y$.
--   6. **Property A** (p. 69). The paper: "A $d$-polytope $Q$ will be said to have property A provided the number of facets of $Q$ is between $2d$ and $2d+2$, and the following condition is satisfied: If the facets of $Q$ are divided into two disjoint classes $\mathfrak X$ and $\mathfrak Y$, each consisting of at most $d+1$ facets, if $X$ (respectively $Y$) denotes the set of all vertices of $Q$ which are entirely surrounded by members of $\mathfrak X$ (respectively $\mathfrak Y$), and if neither $X$ nor $Y$ is empty, then $Q$ admits a path of length at most $d$ joining a member of $X$ to a member of $Y$." Here $Q$ is a bounded face of $P$ of dimension $m=\dim Q$ (in 4.2, $Q=P$ and $m=3$; in 4.1, $Q$ is a $(d-2)$-face). The facets of $Q$ are the faces of $P$ contained in $Q$ of dimension $m-1$; a vertex of $Q$ is entirely surrounded by members of $\mathfrak X$ when every facet of $Q$ through it is in $\mathfrak X$; the classes partition all facets of $Q$; the path runs along edges of $Q$ and has length at most $m$.
--
--   These are the objects of every statement of both missions of this paper (the bounded 5-step conjecture and the 4-step counterexample).
--
--   **Formalization Note** The polyhedron, edges, walks and distance come from the published definitions `Hirsch_model` (`Hirsch.Hpoly`, `Hirsch.Adj`, `Hirsch.DiamLE`) and `Hirsch_walk` (`Hirsch.Reach P L x y`: a walk of $L$ steps, each stationary or along an edge, i.e. $\delta_P(x,y)\le L$). `IsFacetPresentation` is the same notion as `SantosHirsch.Counter.IsFacetPresentation` (redefined here because that module also carries Santos's data tables). `TightSet` has the convention of the platform's `Hirsch.TightSet`, redefined because `Hirsch_simple_vertex` is published only in Mathlib environment `c5ea00351c…`, not in this mission's environment `0df444a3…`, so its module cannot be imported here. On a facet presentation of a pointed $d$-polyhedron, "every vertex lies on exactly $d$ facets" is equivalent to the paper's definition "each of its vertices is incident to exactly $d$ edges" (p. 56). Facet counts use `Set.encard` (values in $\mathbb N\cup\{\infty\}$), so no count is silently truncated. A Dantzig figure keeps $n=2d$ in the type of the row index, `Fin (2 * d)`.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), pp. 55–57, §1 (polyhedron, faces, dimension, vertices, edges, facets, pointed, simple, path, distance, facial path, v-facets); p. 63 (Dantzig figure); p. 69 (property A)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- `(a, b)` is a **facet presentation** of a `d`-polyhedron with `n` facets: the polyhedron
`Hirsch.Hpoly a b = {x | ⟪a i, x⟫ ≤ b i ∀ i}` has nonempty interior in `ℝ^d` (so it is a
nonempty `d`-dimensional polyhedron), and every row is irredundant (dropping row `i` admits a
point violating it). Then the `n` rows are in bijection with the facets of the polyhedron. -/
def IsFacetPresentation {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Prop :=
  (interior (Hirsch.Hpoly a b)).Nonempty ∧
    ∀ i, ∃ x : EuclideanSpace ℝ (Fin d), (∀ j, j ≠ i → ⟪a j, x⟫ ≤ b j) ∧ b i < ⟪a i, x⟫

/-- The rows tight at `v`: on a facet presentation, the facets incident to `v`
(the paper's `v`-facets). Same convention as the platform's `Hirsch.TightSet`. -/
def TightSet {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Set (Fin n) :=
  {i | ⟪a i, v⟫ = b i}

/-- **Simple**: the polyhedron has at least one vertex (it is pointed) and every vertex
(extreme point) lies on exactly `d` of the facets. -/
def IsSimple {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) : Prop :=
  (Set.extremePoints ℝ (Hirsch.Hpoly a b)).Nonempty ∧
    ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b), (TightSet a b v).ncard = d

/-- The set of points of the polyhedron where every row of `I` is tight. -/
def faceOf {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (I : Finset (Fin n)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ Hirsch.Hpoly a b ∧ ∀ i ∈ I, ⟪a i, x⟫ = b i}

/-- A **face** of the polyhedron (the polyhedron itself or its intersection with a supporting
hyperplane): a nonempty set of the form `faceOf a b I`. The empty set is not a face. -/
def IsFace {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  K.Nonempty ∧ ∃ I : Finset (Fin n), K = faceOf a b I

/-- The **dimension** of a set: the dimension of its affine hull. -/
noncomputable def dim {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ K).direction

/-- The faces `K₁, …, K_r` (`r` = length of `ks`) form a **`(k₁, …, k_r)`-path from `x` to `y`**
(p. 57): each `K_i` is a face of dimension `k_i`, consecutive faces meet, `x ∈ K₁`, `y ∈ K_r`. -/
def FacialPathFaces {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (ks : List ℕ) (x y : EuclideanSpace ℝ (Fin d))
    (K : Fin ks.length → Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ i, IsFace a b (K i) ∧ dim (K i) = ks.get i) ∧
    (∀ i j : Fin ks.length, j.val = i.val + 1 → (K i ∩ K j).Nonempty) ∧
    ∃ h : 0 < ks.length, x ∈ K ⟨0, h⟩ ∧ y ∈ K ⟨ks.length - 1, Nat.sub_lt h Nat.one_pos⟩

/-- The polyhedron admits a `(k₁, …, k_r)`-path from `x` to `y`. -/
def IsFacialPath {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (ks : List ℕ) (x y : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ K : Fin ks.length → Set (EuclideanSpace ℝ (Fin d)), FacialPathFaces a b ks x y K

/-- The polyhedron admits a `(k₁, …, k_r)`-path from `x` to `y`, no member of which lies
entirely within the set `F`. -/
def IsFacialPathAvoiding {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (ks : List ℕ) (x y : EuclideanSpace ℝ (Fin d)) (F : Set (EuclideanSpace ℝ (Fin d))) :
    Prop :=
  ∃ K : Fin ks.length → Set (EuclideanSpace ℝ (Fin d)),
    FacialPathFaces a b ks x y K ∧ ∀ i, ¬ K i ⊆ F

/-- `(P, x, y)` is a **`d`-dimensional Dantzig figure** (p. 63): `P` is a `d`-polyhedron with
`2d` facets (a facet presentation with `2d` rows), `x` and `y` are vertices, exactly `d`
facets are incident to `x` and exactly `d` others are incident to `y`. -/
def IsDantzigFigure {d : ℕ} (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : Prop :=
  IsFacetPresentation a b ∧
    x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b) ∧
    (TightSet a b x).ncard = d ∧ (TightSet a b y).ncard = d ∧
    Disjoint (TightSet a b x) (TightSet a b y)

/-- The **facets of a face `Q`**: the faces of the polyhedron contained in `Q` whose dimension
is one less than that of `Q`. -/
def facetsOfFace {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (Q : Set (EuclideanSpace ℝ (Fin d))) : Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {K | IsFace a b K ∧ K ⊆ Q ∧ dim K + 1 = dim Q}

/-- The vertices of the face `Q` **entirely surrounded by members of `𝔛`**: the vertices of `Q`
every facet of `Q` through which belongs to `𝔛`. -/
def surroundedBy {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (Q : Set (EuclideanSpace ℝ (Fin d))) (𝔛 : Set (Set (EuclideanSpace ℝ (Fin d)))) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {v | v ∈ Set.extremePoints ℝ Q ∧ ∀ K ∈ facetsOfFace a b Q, v ∈ K → K ∈ 𝔛}

/-- **Property A** (p. 69) of a face `Q` of the polyhedron, a polytope of dimension
`m = dim Q`: `Q` is a bounded face, the number of facets of `Q` is between `2m` and `2m + 2`,
and whenever the facets of `Q` are divided into two disjoint classes `𝔛` and `𝔜` of at most
`m + 1` facets each such that the sets `X`, `Y` of vertices of `Q` entirely surrounded by
members of `𝔛`, resp. `𝔜`, are both nonempty, some member of `X` is joined to some member of
`Y` by a path of length at most `m` in `Q`. -/
def HasPropertyA {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (Q : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsFace a b Q ∧ Bornology.IsBounded Q ∧
    ((2 * dim Q : ℕ) : ℕ∞) ≤ (facetsOfFace a b Q).encard ∧
    (facetsOfFace a b Q).encard ≤ ((2 * dim Q + 2 : ℕ) : ℕ∞) ∧
    ∀ 𝔛 𝔜 : Set (Set (EuclideanSpace ℝ (Fin d))),
      𝔛 ∪ 𝔜 = facetsOfFace a b Q → Disjoint 𝔛 𝔜 →
      𝔛.encard ≤ ((dim Q + 1 : ℕ) : ℕ∞) → 𝔜.encard ≤ ((dim Q + 1 : ℕ) : ℕ∞) →
      (surroundedBy a b Q 𝔛).Nonempty → (surroundedBy a b Q 𝔜).Nonempty →
      ∃ u ∈ surroundedBy a b Q 𝔛, ∃ v ∈ surroundedBy a b Q 𝔜, Hirsch.Reach Q (dim Q) u v

end KleeWalkup67.FiveStep


