-- Prove2me | Definitions.Def_FourColorLinear_Occurrence
-- name    : FourColorLinear_Occurrence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:49.543547+00:00
-- url     : https://prove2.me/theorems/b88c2627-10ab-41e8-948d-ef83ca89280f
-- title:
--   Occurrences of a configuration in a plane graph and non-touching families
-- statement:
--   A plane graph $G$ **contains** a configuration $C$ if there is a homomorphism $\hat Z\to G$ that is injective on $Z$, gives each vertex of $Z$ its degree $\delta$ in $G$, and carries the rotation at each vertex of $Z$ to the rotation of $G$ there. The homomorphism "may not be 1-1 on $R(Z)$". The occurrence is **induced** if $Z$ is an induced subgraph of $G$.
--
--   Since $\hat Z$ is embedded, this gives all of p.3: inner faces of $Z$ are faces of $G$, they have one common orientation, and the two outside neighbours of a cut vertex are non-consecutive. The common orientation may be that of the mirror image.
--
--   An occurrence induces a ring coloring from any coloring of $G$. The companions of this definition fix the input words of a family of occurrences and of a partial coloring (the value $4$ meaning "uncolored"), and the notion of a family of pairwise non-touching induced occurrences.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), §1.1, p.3; §1.2, p.5

import Mathlib
import Definitions.Def_FourColorLinear_Config
import Definitions.Def_FourColorLinear_encodeAdj

open PlanarQueue.Genus

namespace FourColorLinear

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- An occurrence of a configuration in a plane graph (arXiv:2610.39753, held version, sha256
4dce39c5…, p.3): "Z is embedded in G such that every inner triangular face of Z is also a face in
G, and all triangular faces of Z have the same orientation in G. Moreover, we require that the degree
of each vertex v ∈ V(Z) in G is equal to δ(v) … the embedding ϕ of Z into G can be extended to a
homomorphism ϕ from Ẑ into G, but this homomorphism may not be 1-1 on R(Z)."

**Formalization Note** `hom` is the extended homomorphism on the free completion, injective on `Z`,
with degree `δ` on `Z`. Rotation at each vertex of `Z` is carried to rotation; this yields the
face clause, the orientation clause and the cut-vertex clause "non-consecutive around v". `mirror`
is the common orientation: p.3 asks that all faces have "the same orientation", which allows the
reflection of the whole configuration. -/
structure Occurrence (S : EmbeddingScheme G) (C : Config) where
  /-- the homomorphism `Ẑ → G` -/
  hom : C.G →g G
  /-- whether the whole configuration occurs reflected -/
  mirror : Bool
  inj : Set.InjOn hom C.Z
  degree_eq : ∀ v ∈ C.Z, G.degree (hom v) = C.G.degree v
  rot_eq : ∀ d : C.G.Dart, d.fst ∈ C.Z →
    hom.mapDart (C.S.rot d) = (if mirror then S.rot.symm else S.rot) (hom.mapDart d)

namespace Occurrence

variable {S : EmbeddingScheme G} {C : Config}

/-- The vertex set of the image of `Z`. -/
def verts (O : Occurrence S C) : Set (Fin n) := O.hom '' C.Z

/-- Induced (p.3): "Z is an induced subgraph of G". -/
def Induced (O : Occurrence S C) : Prop :=
  ∀ u ∈ C.Z, ∀ v ∈ C.Z, G.Adj (O.hom u) (O.hom v) → C.G.Adj u v

/-- The coloring a coloring of `G` induces on the ring (p.3). -/
def ringColoring (O : Occurrence S C) (ψ : Fin n → Fin 4) : Fin C.R → Fin 4 :=
  fun i => ψ (O.hom (C.ring i))

end Occurrence

/-- An occurrence in `G` of a member of the list `𝒟`. -/
abbrev OccIn (S : EmbeddingScheme G) (𝒟 : List Config) : Type :=
  Σ i : Fin 𝒟.length, Occurrence S 𝒟[i]

/-- A family of pairwise non-touching induced occurrences (p.5, Theorem 3(a); p.8, Task 5). -/
def IsNonTouchingFamily {S : EmbeddingScheme G} {𝒟 : List Config} (Zs : List (OccIn S 𝒟)) : Prop :=
  (∀ z ∈ Zs, z.2.Induced) ∧ Zs.Pairwise fun a b => ¬ Touch G a.2.verts b.2.verts

/-- The vertices of the configurations in a list. -/
def covered {S : EmbeddingScheme G} {𝒟 : List Config} (Zs : List (OccIn S 𝒟)) : Set (Fin n) :=
  {v | ∃ z ∈ Zs, v ∈ z.2.verts}

/-- The words of a family: its length, then for each member its index in `𝒟` and the values of the
homomorphism on the vertices of its free completion. -/
def encodeFamily {S : EmbeddingScheme G} {𝒟 : List Config} (Zs : List (OccIn S 𝒟)) : List ℕ :=
  Zs.length :: Zs.flatMap fun z => z.1.val :: List.ofFn fun x => (z.2.hom x).val

open Classical in
/-- The words of a coloring of `G − ⋃ Z′`: its color per vertex, and `4` for "uncolored" (p.14:
"we use a third bit for 'uncolored'"). -/
noncomputable def encodeColoring (X : Set (Fin n)) (ψ : Fin n → Fin 4) : List ℕ :=
  List.ofFn fun v => if v ∈ X then 4 else (ψ v).val

/-- The members of `Zs` selected by a list of indices. -/
def selected {α : Type} (Zs : List α) (idx : List ℕ) : List α := idx.filterMap fun j => Zs[j]?

/-- A strictly increasing list of indices into a list of length `L`: a subfamily. -/
def IsIndexList (L : ℕ) (idx : List ℕ) : Prop := idx.Pairwise (· < ·) ∧ ∀ j ∈ idx, j < L

end FourColorLinear


