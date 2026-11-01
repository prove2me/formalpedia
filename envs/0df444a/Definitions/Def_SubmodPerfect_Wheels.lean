-- Prove2me | Definitions.Def_SubmodPerfect_Wheels
-- name    : SubmodPerfect_Wheels
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:45.502749+00:00
-- url     : https://prove2.me/theorems/6d9b4829-a50e-44a8-afe6-401caf0b8ae5
-- title:
--   Breaking, paws, paw-friendly graphs, wheels, sectors, segments and bicolorings
-- statement:
--   Let $G$ be a finite graph.
--
--   1. For $U\subseteq V(G)$, a vertex $v\in U$ and $X\subseteq U\setminus\{v\}$, **$v$ breaks $X$** in $G[U]$ if for every connected component $D$ of $G[U]\setminus N[v]$ we have $X\not\subseteq N[D]$ (neighbourhoods in $G[U]$).
--   2. A **paw** with vertex set $\{a,c,b_1,b_2\}$ and edge set $\{ab_1,ab_2,b_1b_2,ac\}$ is an induced subgraph with exactly these edges.
--   3. $G$ is **paw-friendly** if $G$ is perfect and for every induced subgraph $H$ and every such paw in $H$, with respect to $H$ either $a$ breaks $\{c,b_1,b_2\}$, or $b_1$ breaks $\{c,b_2\}$, or $b_2$ breaks $\{c,b_1\}$.
--   4. A **wheel** $(H,v)$ is a hole $H$ and a vertex $v\notin H$ with at least three neighbours in $H$. A **sector** is a subpath of $H$ of length at least one whose ends are adjacent to $v$ and whose interior is not; it is **short** if it has length one. The wheel is **odd** if it has an odd number of short sectors, **universal** if $v$ is complete to $H$, a **line wheel** if it has exactly four sectors, exactly two of them short and vertex-disjoint, a **twin wheel** if it has exactly three sectors, exactly two of them short, **triangle-free** if $H\cup\{v\}$ has no triangle, and **proper** if it is none of universal, twin, triangle-free.
--   5. A **segment** of a wheel is a maximal subpath $Q$ of $H$ (length $0$ allowed) with $Q\cup\{v\}$ triangle-free; segments $Q,Q'$ are **adjacent** if $Q\cup Q'\cup\{v\}$ has a triangle. A **bicoloring** of a proper wheel that is not odd is a partition of $V(H)$ into nonempty $R,B$ in which every segment is monochromatic and adjacent segments get different colours.
--   6. For disjoint anticomplete $A,B$, a **path from $A$ to $B$** is an inclusion-wise minimal induced path of $G\setminus(A\cup B)$ whose first vertex has a neighbour in $A$ and whose last vertex has a neighbour in $B$.
--   7. A **cutset** is a set $K$ with $G\setminus K$ not connected; $K$ **separates** $x$ from $y$ if both lie outside $K$ and every walk from $x$ to $y$ meets $K$.
--
--   These notions carry Section 5, where paws are shown to be forcers in (C4, prism)-free perfect graphs.
--
--   **Formalization Note** Subpaths of a hole are induced paths of $G$ inside it, and sectors are counted as vertex sets. The condition $v\notin X$ in "v breaks X" is the domain of the paper's definition and is part of the Lean predicate.
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, §4, p.14 (breaks); §5, p.15 (paw), p.16 (wheels, sectors, segments), p.17 (bicoloring, path from A to B), p.19 (paw-friendly); §1, p.4 (cutset)

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_SubmodPerfect_Graphs

set_option autoImplicit false
open Classical
open scoped BigOperators

noncomputable section

namespace SubmodPerfect

/-! # Breaking, paws, paw-friendly graphs, wheels, segments and bicolorings

Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*,
arXiv:2110.00108v2: breaking (§4, p.14), paws (§5, p.15), linking onto a triangle is not used,
wheels and their sectors (§5, p.16), segments (p.16), bicolorings and paths from `A` to `B`
(p.17), paw-friendly graphs (p.19), cutsets (p.4).

**Formalization Note.** Holes are cyclic lists in the sense of the published
`StrongPerfectGraph.OddPrism.IsHole`; a *subpath* of a hole `H` is an induced path of `G` whose
vertices all lie in `H` (inside a hole these are exactly the arcs of the cycle). Sectors are
counted as vertex sets, so a path and its reversal count once. -/

variable {V : Type*} [Fintype V]

/-- `v` breaks `X` in `G[U]` (p.14): `v` is a vertex of `U` not in `X`, and for every
connected component `D` of `G[U] \ N[v]` we have `X ⊄ N[D]`, neighbourhoods taken in `G[U]`.

**Formalization Note.** The paper defines "v breaks X" for `v ∈ V(G) \ X` only; that domain
condition is part of the definition. The condition is vacuous when `G[U] \ N[v]` is empty. -/
def BreaksIn (G : SimpleGraph V) (U : Finset V) (v : V) (X : Finset V) : Prop :=
  v ∈ U ∧ v ∉ X ∧
    ∀ D, IsComponentIn G (U \ closedNbhdIn G U {v}) D → ¬ X ⊆ closedNbhdIn G U D

/-- `{a, c, b₁, b₂}` is a paw with edge set `{ab₁, ab₂, b₁b₂, ac}` (p.15, p.19): four distinct
vertices inducing exactly these four edges (so `c` is non-adjacent to `b₁` and `b₂`). -/
def IsPaw (G : SimpleGraph V) (a c b₁ b₂ : V) : Prop :=
  a ≠ c ∧ a ≠ b₁ ∧ a ≠ b₂ ∧ c ≠ b₁ ∧ c ≠ b₂ ∧ b₁ ≠ b₂ ∧
    G.Adj a b₁ ∧ G.Adj a b₂ ∧ G.Adj b₁ b₂ ∧ G.Adj a c ∧ ¬ G.Adj c b₁ ∧ ¬ G.Adj c b₂

/-- `G` is paw-friendly (p.19): `G` is perfect, and for every induced subgraph `H = G[U]` and
every paw of `H` with vertex set `{c, a, b₁, b₂}` and edge set `{ab₁, ab₂, b₁b₂, ac}`, with
respect to `H` either `a` breaks `{c, b₁, b₂}`, or `b₁` breaks `{c, b₂}`, or `b₂` breaks
`{c, b₁}`. -/
def IsPawFriendly (G : SimpleGraph V) : Prop :=
  StrongPerfectGraph.Main.IsPerfect G ∧
    ∀ U : Finset V, ∀ a c b₁ b₂ : V, a ∈ U → c ∈ U → b₁ ∈ U → b₂ ∈ U → IsPaw G a c b₁ b₂ →
      BreaksIn G U a {c, b₁, b₂} ∨ BreaksIn G U b₁ {c, b₂} ∨ BreaksIn G U b₂ {c, b₁}

/-- `P` is a subpath of the hole `H`: an induced path of `G` all of whose vertices lie in `H`. -/
def IsSubpathOf (G : SimpleGraph V) (H P : List V) : Prop :=
  StrongPerfectGraph.OddPrism.IsInducedPath G P ∧ ∀ x ∈ P, x ∈ H

/-- `(H, v)` is a wheel (p.16): `H` is a hole, `v ∉ H`, and `v` has at least three neighbours
in `H`. -/
def IsWheel (G : SimpleGraph V) (H : List V) (v : V) : Prop :=
  StrongPerfectGraph.OddPrism.IsHole G H ∧ v ∉ H ∧
    3 ≤ (H.toFinset.filter (fun x => G.Adj v x)).card

/-- `P` is a sector of `(H, v)` (p.16): a subpath of `H` of length at least one such that `v` is
complete to its two ends and anticomplete to its interior. -/
def IsSector (G : SimpleGraph V) (H : List V) (v : V) (P : List V) : Prop :=
  IsSubpathOf G H P ∧ 2 ≤ P.length ∧
    (∀ x, P.head? = some x → G.Adj v x) ∧ (∀ x, P.getLast? = some x → G.Adj v x) ∧
    ∀ i : Fin P.length, 0 < i.val → i.val + 1 < P.length → ¬ G.Adj v (P.get i)

/-- The sectors of `(H, v)`, as vertex sets. -/
def sectorSets (G : SimpleGraph V) (H : List V) (v : V) : Set (Finset V) :=
  {S | ∃ P, IsSector G H v P ∧ P.toFinset = S}

/-- The short sectors of `(H, v)` (p.16): sectors of length one, i.e. with two vertices. -/
def shortSectorSets (G : SimpleGraph V) (H : List V) (v : V) : Set (Finset V) :=
  {S | S ∈ sectorSets G H v ∧ S.card = 2}

/-- An odd wheel (p.16): a wheel with an odd number of short sectors. -/
def IsOddWheel (G : SimpleGraph V) (H : List V) (v : V) : Prop :=
  IsWheel G H v ∧ Odd (shortSectorSets G H v).ncard

/-- A universal wheel (p.16): `v` is complete to `H`. -/
def IsUniversalWheel (G : SimpleGraph V) (H : List V) (v : V) : Prop :=
  IsWheel G H v ∧ ∀ x ∈ H, G.Adj v x

/-- A line wheel (p.16): exactly four sectors, exactly two of them short, and the two short
sectors have no common vertex. -/
def IsLineWheel (G : SimpleGraph V) (H : List V) (v : V) : Prop :=
  IsWheel G H v ∧ (sectorSets G H v).ncard = 4 ∧ (shortSectorSets G H v).ncard = 2 ∧
    ∀ S ∈ shortSectorSets G H v, ∀ T ∈ shortSectorSets G H v, S ≠ T → Disjoint S T

/-- A twin wheel (p.16): exactly three sectors, exactly two of them short. -/
def IsTwinWheel (G : SimpleGraph V) (H : List V) (v : V) : Prop :=
  IsWheel G H v ∧ (sectorSets G H v).ncard = 3 ∧ (shortSectorSets G H v).ncard = 2

/-- `T` induces a triangle-free graph. -/
def IsTriangleFreeSet (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T, G.Adj x y → G.Adj y z → G.Adj x z → False

/-- A triangle-free wheel (p.16): the wheel `H ∪ {v}` contains no triangle. -/
def IsTriangleFreeWheel (G : SimpleGraph V) (H : List V) (v : V) : Prop :=
  IsWheel G H v ∧ IsTriangleFreeSet G (insert v H.toFinset)

/-- A proper wheel (p.16): a wheel that is not a universal, a twin, or a triangle-free wheel. -/
def IsProperWheel (G : SimpleGraph V) (H : List V) (v : V) : Prop :=
  IsWheel G H v ∧ ¬ IsUniversalWheel G H v ∧ ¬ IsTwinWheel G H v ∧ ¬ IsTriangleFreeWheel G H v

/-- `S` is (the vertex set of) a segment of the wheel `(H, v)` (p.16): a maximal subpath `Q` of
`H` (length `0` allowed) such that `Q ∪ {v}` is triangle-free. Maximality is with respect to
inclusion among subpaths of `H` with that property. -/
def IsSegment (G : SimpleGraph V) (H : List V) (v : V) (S : Finset V) : Prop :=
  (∃ Q, IsSubpathOf G H Q ∧ Q.toFinset = S) ∧ IsTriangleFreeSet G (insert v S) ∧
    ∀ S' : Finset V, (∃ Q', IsSubpathOf G H Q' ∧ Q'.toFinset = S') → S ⊆ S' →
      IsTriangleFreeSet G (insert v S') → S' = S

/-- Two segments `S, S'` of `(H, v)` are adjacent (p.16): `S ∪ S' ∪ {v}` contains a triangle. -/
def AreAdjacentSegments (G : SimpleGraph V) (H : List V) (v : V) (S S' : Finset V) : Prop :=
  IsSegment G H v S ∧ IsSegment G H v S' ∧ ¬ IsTriangleFreeSet G (insert v (S ∪ S'))

/-- `R, B` is a bicoloring of the proper, non-odd wheel `(H, v)` (p.17): a partition of the
vertices of `H` into nonempty sets `R` and `B` such that the vertices of each segment have the
same colour and vertices of adjacent segments have distinct colours. -/
def IsBicoloring (G : SimpleGraph V) (H : List V) (v : V) (R B : Finset V) : Prop :=
  IsProperWheel G H v ∧ ¬ IsOddWheel G H v ∧
    Disjoint R B ∧ R ∪ B = H.toFinset ∧ R.Nonempty ∧ B.Nonempty ∧
    (∀ S, IsSegment G H v S → S ⊆ R ∨ S ⊆ B) ∧
    ∀ S S', AreAdjacentSegments G H v S S' → ¬ (S ⊆ R ∧ S' ⊆ R) ∧ ¬ (S ⊆ B ∧ S' ⊆ B)

/-- `P` is a path from `A` to `B` (p.17), for disjoint, anticomplete `A`, `B`: an induced path
`x₁-…-xₙ` of `G \ (A ∪ B)` such that `x₁` has a neighbour in `A` and `xₙ` has a neighbour in
`B`, and `P` is inclusion-wise minimal with this property. -/
def IsPathFromSetTo (G : SimpleGraph V) (A B : Finset V) (P : List V) : Prop :=
  let ok : List V → Prop := fun Q =>
    StrongPerfectGraph.OddPrism.IsInducedPath G Q ∧ (∀ x ∈ Q, x ∉ A ∧ x ∉ B) ∧
      (∃ x, Q.head? = some x ∧ ∃ a ∈ A, G.Adj x a) ∧
      (∃ y, Q.getLast? = some y ∧ ∃ b ∈ B, G.Adj y b)
  ok P ∧ ∀ Q, ok Q → Q.toFinset ⊆ P.toFinset → Q.toFinset = P.toFinset

/-- `K` is a cutset of `G` (p.4): `G \ K` is not connected. -/
def IsCutset (G : SimpleGraph V) (K : Finset V) : Prop :=
  ¬ (G.induce ((Finset.univ \ K : Finset V) : Set V)).Connected

/-- `K` separates `x` from `y` in `G`: both lie outside `K`, and every walk from `x` to `y`
meets `K`. -/
def Separates (G : SimpleGraph V) (K : Finset V) (x y : V) : Prop :=
  x ∉ K ∧ y ∉ K ∧ ∀ p : G.Walk x y, ∃ z ∈ p.support, z ∈ K

end SubmodPerfect


