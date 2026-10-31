-- Prove2me | Definitions.Def_BimatrixStableSet_Polyhedra
-- name    : BimatrixStableSet_Polyhedra
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:29.282303+00:00
-- url     : https://prove2.me/theorems/9224bee6-0577-4b2c-81f2-a42937361384
-- title:
--   Linear systems, faces (2), dimension, facets, vertices, the graph, simple and dual-neighborly polytopes, combinatorial type
-- statement:
--   This module fixes the polyhedral vocabulary of §2 of the paper.
--
--   1. **Systems and polyhedra** (p.5). A system is a matrix $C\in\mathbb R^{\iota\times N}$ with a right-hand side $q$, and its polyhedron is $\{z\in\mathbb R^N\mid Cz\le q\}$. Row $k$ is **binding** at $z$ if $(Cz)_k=q_k$, and the **labels** of $z$ are its binding rows.
--   2. **Faces** (display (2), p.5). A face is a nonempty set $\{z\mid Cz\le q,\ (Cz)_i=q_i\text{ for }i\in S\}$.
--   3. **Dimension** (p.5). The dimension of a set is that of its affine hull.
--   4. **Facets, vertices, edges** (p.5). For a face $F$, a facet of $F$ is a face $G\subseteq F$ with $\dim G+1=\dim F$. An edge is a face in $F$ of dimension $1$. A vertex is a point $v\in F$ with $\{v\}$ a face.
--   5. **Graph** (p.6). The graph of $F$ has the vertices of $F$ as nodes, and two distinct vertices are adjacent when an edge of $F$ contains both.
--   6. **Simple and dual-neighborly** (pp.5–6). $F$ is simple if every vertex lies in exactly $\dim F$ facets of $F$. A simple $d$-polytope is dual-neighborly if any $\lfloor d/2\rfloor$ of its facets have a non-empty intersection.
--   7. **Redundant rows** (Lemma 3(c), p.7). A row is redundant if deleting it does not change the polyhedron.
--   8. **Combinatorial type** (p.5). Two polytopes have the same type if their face lattices are isomorphic.
--
--   Every later statement about $P$, $Q$ and their facets is written in these terms.
--
--   **Formalization Note** All notions are defined for a face $F$ of a system rather than only for a whole polyhedron. The faces of $F$, as a polytope in its own right, are exactly the faces of the system inside $F$, so a facet of $P\subseteq\mathbb R^5$ is a 4-polytope with no change of coordinates. Faces are nonempty, so the empty face and its dimension $-1$ do not appear, and the relation $\dim G+1=\dim F$ uses no natural-number subtraction. The face poset omits the empty face; two face lattices are isomorphic exactly when these posets are.
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, §2, pp.5–6, display (2); Lemma 3(c), p.7

import Mathlib

open Matrix

namespace BimatrixStableSet

/-- A finite system of linear inequalities `Cz ≤ q` in `ℝᴺ`, with rows indexed by `ι`
(Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, §2, p.5).

**Formalization Note.** The system, not only its solution set, is the primary object: the paper
defines faces by converting inequalities into equalities (display (2)), and later keeps track of
which inequalities are binding, of their labels and of redundant inequalities. -/
structure System (ι : Type) (N : ℕ) where
  /-- The coefficient matrix `C`. -/
  C : Matrix ι (Fin N) ℝ
  /-- The right-hand side `q`. -/
  q : ι → ℝ

/-- The dimension of a set of points: the dimension of its affine hull, p.5 ("A convex set has
dimension `d` if and only if it has `d + 1`, but no more, affinely independent points").

**Formalization Note.** The value on the empty set is `0`. Dimension is only ever applied to faces,
which are nonempty by `System.IsFace`, so the paper's "dimension `-1`" never arises. -/
noncomputable def faceDim {N : ℕ} (F : Set (Fin N → ℝ)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)

namespace System

variable {ι : Type} {N : ℕ} (Z : System ι N)

/-- The polyhedron `{z ∈ ℝᴺ | Cz ≤ q}`, p.5. -/
def carrier : Set (Fin N → ℝ) := {z | ∀ k, (Z.C *ᵥ z) k ≤ Z.q k}

/-- Row `k` is binding at `z`: it holds as an equality. -/
def IsBinding (z : Fin N → ℝ) (k : ι) : Prop := (Z.C *ᵥ z) k = Z.q k

/-- The labels of a point: the binding rows, p.7 ("its labels are the labels of the binding
inequalities for that point"). The label of a row is the row index itself. -/
def labels (z : Fin N → ℝ) : Set ι := {k | Z.IsBinding z k}

/-- The set of display (2), p.5: `{z | Cz ≤ q, (Cz)ᵢ = qᵢ for i ∈ S}`. -/
def face (S : Set ι) : Set (Fin N → ℝ) := {z | z ∈ Z.carrier ∧ ∀ k ∈ S, Z.IsBinding z k}

/-- `F` is a face of the system: a nonempty set of the form (2).

**Formalization Note.** The empty face is excluded, so `faceDim` needs no value `-1`. The faces of a
face `F`, regarded as a polytope in its own right, are exactly the faces of the system contained in
`F`, because the system of `F` is the given system with some inequalities turned into equalities.
Hence everything below is defined for a face `F` of a system. In particular a facet of `P ⊆ ℝ⁵` is
a 4-polytope without any change of coordinates. -/
def IsFace (F : Set (Fin N → ℝ)) : Prop := F.Nonempty ∧ ∃ S : Set ι, F = Z.face S

/-- `G` is a facet of the face `F`: a face of the system inside `F` with `dim G = dim F - 1`, p.5.

**Formalization Note.** Stated as `dim G + 1 = dim F`, with no natural-number subtraction. A vertex
has no facets, in agreement with the paper's convention that a facet of a polytope contains
points. -/
def IsFacetOf (G F : Set (Fin N → ℝ)) : Prop :=
  Z.IsFace G ∧ G ⊆ F ∧ faceDim G + 1 = faceDim F

/-- The set of facets of `F`. It is finite for finite `ι`, since a face is `Z.face S` for one of
finitely many `S`. -/
def facets (F : Set (Fin N → ℝ)) : Set (Set (Fin N → ℝ)) := {G | Z.IsFacetOf G F}

/-- The vertices of `F`: the points `v ∈ F` such that `{v}` is a face, p.5 ("A vertex is a singleton
`{v}` and also identified with `v`"). A nonempty face has dimension `0` if and only if it is a
singleton. -/
def vertices (F : Set (Fin N → ℝ)) : Set (Fin N → ℝ) := {v | v ∈ F ∧ Z.IsFace {v}}

/-- `E` is an edge of `F`: a face of dimension `1` inside `F`, p.5. -/
def IsEdgeOf (E F : Set (Fin N → ℝ)) : Prop := Z.IsFace E ∧ E ⊆ F ∧ faceDim E = 1

/-- `u` and `v` are distinct vertices of `F` that are endpoints of an edge of `F`, p.6 ("then `u`
and `v` are also called adjacent"). -/
def AdjIn (F : Set (Fin N → ℝ)) (u v : Fin N → ℝ) : Prop :=
  u ≠ v ∧ u ∈ Z.vertices F ∧ v ∈ Z.vertices F ∧ ∃ E, Z.IsEdgeOf E F ∧ u ∈ E ∧ v ∈ E

/-- The graph of the polytope `F`, p.6, on the vertices of `F`. -/
def graph (F : Set (Fin N → ℝ)) : SimpleGraph (Z.vertices F) where
  Adj u v := Z.AdjIn F u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.imp fun _ e => ⟨e.1, e.2.2, e.2.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `F` is simple: every vertex of `F` belongs to exactly `dim F` facets of `F`, p.5. -/
def IsSimple (F : Set (Fin N → ℝ)) : Prop :=
  ∀ v ∈ Z.vertices F, {G | Z.IsFacetOf G F ∧ v ∈ G}.ncard = faceDim F

/-- `F` is a `d`-polytope: a bounded face of dimension `d`, p.5. -/
def IsPolytopeOfDim (F : Set (Fin N → ℝ)) (d : ℕ) : Prop :=
  Z.IsFace F ∧ Bornology.IsBounded F ∧ faceDim F = d

/-- `F` is a simple `d`-polytope, p.5. -/
def IsSimplePolytopeOfDim (F : Set (Fin N → ℝ)) (d : ℕ) : Prop :=
  Z.IsPolytopeOfDim F d ∧ Z.IsSimple F

/-- A simple `d`-polytope is dual-neighborly if any `⌊d/2⌋` of its facets have a non-empty
intersection, p.6.

**Formalization Note.** "Any `⌊d/2⌋` of its facets" is a set `T` of `⌊d/2⌋` distinct facets. For
`d ∈ {4, 5}` this says that any two facets meet. -/
def IsDualNeighborly (F : Set (Fin N → ℝ)) : Prop :=
  ∀ T : Finset (Set (Fin N → ℝ)), (∀ G ∈ T, Z.IsFacetOf G F) → T.card = faceDim F / 2 →
    (⋂ G ∈ T, G).Nonempty

/-- Row `k` is redundant: it "can be omitted without changing the polytope", Lemma 3(c), p.7. -/
def IsRedundant (k : ι) : Prop :=
  {z : Fin N → ℝ | ∀ l, l ≠ k → (Z.C *ᵥ z) l ≤ Z.q l} = Z.carrier

/-- The poset of (nonempty) faces of `F`, ordered by inclusion, p.5.

**Formalization Note.** The paper's face lattice also has the empty face as a bottom element. Two
such lattices are isomorphic if and only if these posets are. -/
abbrev FacePoset (F : Set (Fin N → ℝ)) : Type := {G : Set (Fin N → ℝ) // Z.IsFace G ∧ G ⊆ F}

/-- `F` and `F'` have the same combinatorial type: their face lattices are isomorphic, p.5. The two
faces may live in different systems and different ambient dimensions. -/
def SameType {ι' : Type} {N' : ℕ} (F : Set (Fin N → ℝ)) (Z' : System ι' N')
    (F' : Set (Fin N' → ℝ)) : Prop :=
  Nonempty (Z.FacePoset F ≃o Z'.FacePoset F')

end System

end BimatrixStableSet


