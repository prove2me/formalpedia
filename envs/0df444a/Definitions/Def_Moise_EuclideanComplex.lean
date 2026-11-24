-- Prove2me | Definitions.Def_Moise_EuclideanComplex
-- name    : Moise_EuclideanComplex
-- status  : Definition
-- author  : @wojtek_politarczyk
-- created : 2026-11-24T13:27:34.099688+00:00
-- url     : https://prove2.me/theorems/bde75727-e5e6-4e3d-91d3-aaa990a4238d
-- title:
--   Euclidean complexes, skeletons, polyhedra, triangulations, subdivisions, and PL maps
-- statement:
--   Defines the foundational objects of Moise Chapters 1–2 in $\mathbb{R}^n$: affine simplices `Moise.Simplex`, Euclidean complexes `Moise.EuclideanComplex`, finiteness `Moise.EuclideanComplex.IsFinite`, $d$-skeletons `Moise.EuclideanComplex.skeleton`, polyhedra `Moise.EuclideanComplex.polyhedron`, triangulations `Moise.Triangulation`, subdivisions `Moise.EuclideanComplex.IsSubdivision`, simplicial maps `Moise.IsSimplicialMap`, PL maps `Moise.IsPLMap`, and PL homeomorphisms `Moise.IsPLHomeomorph`.
-- source:
--   E. E. Moise, Geometric Topology in Dimensions 2 and 3, Springer GTM 47, 1977, Chapters 1–2, pp. 1–16.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Topology.Order.Basic

namespace Moise

/-- An affine simplex in `ℝⁿ` is represented by its finite, nonempty, affinely independent
vertex set `vertices : Finset (EuclideanSpace ℝ (Fin n))`. Its dimension is `vertices.card - 1`. -/
structure Simplex (n : ℕ) where
  vertices : Finset (EuclideanSpace ℝ (Fin n))
  nonempty : vertices.Nonempty
  affineIndep : AffineIndependent ℝ (fun v : vertices => (v : EuclideanSpace ℝ (Fin n)))

/-- The geometric realization (convex hull) of a simplex in `ℝⁿ`. -/
def Simplex.carrier {n : ℕ} (σ : Simplex n) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ (σ.vertices : Set (EuclideanSpace ℝ (Fin n)))

/-- The dimension of a simplex (`vertices.card - 1`). -/
def Simplex.dim {n : ℕ} (σ : Simplex n) : ℕ :=
  σ.vertices.card - 1

/-- `τ` is a face of `σ` if `τ.vertices ⊆ σ.vertices`. -/
def Simplex.IsFace {n : ℕ} (τ σ : Simplex n) : Prop :=
  τ.vertices ⊆ σ.vertices

/-- A Euclidean complex in `ℝⁿ` (Moise, Ch. 1–2): a locally finite collection of simplices in `ℝⁿ`
closed under taking faces, such that any two simplices meet in either the empty set or a common face. -/
structure EuclideanComplex (n : ℕ) where
  simplices : Set (Simplex n)
  locallyFinite : LocallyFinite (fun σ : simplices => σ.1.carrier)
  face_closed : ∀ {σ τ : Simplex n}, σ ∈ simplices → τ.IsFace σ → τ ∈ simplices
  inter_face : ∀ {σ₁ σ₂ : Simplex n}, σ₁ ∈ simplices → σ₂ ∈ simplices →
    (σ₁.carrier ∩ σ₂.carrier).Nonempty →
    ∃ τ ∈ simplices, τ.IsFace σ₁ ∧ τ.IsFace σ₂ ∧ τ.carrier = σ₁.carrier ∩ σ₂.carrier

/-- A Euclidean complex is finite if it has finitely many simplices. -/
def EuclideanComplex.IsFinite {n : ℕ} (K : EuclideanComplex n) : Prop :=
  K.simplices.Finite

/-- The vertex set of a Euclidean complex `K`. -/
def EuclideanComplex.vertices {n : ℕ} (K : EuclideanComplex n) : Set (EuclideanSpace ℝ (Fin n)) :=
  ⋃ σ ∈ K.simplices, (σ.vertices : Set (EuclideanSpace ℝ (Fin n)))

/-- The `d`-skeleton of a Euclidean complex `K`: the subcomplex of simplices of dimension `≤ d`. -/
def EuclideanComplex.skeleton {n : ℕ} (K : EuclideanComplex n) (d : ℕ) : EuclideanComplex n where
  simplices := {σ ∈ K.simplices | σ.dim ≤ d}
  locallyFinite := fun x => by
    obtain ⟨U, hU, hfin⟩ := K.locallyFinite x
    refine ⟨U, hU, ?_⟩
    have : {σ : {σ ∈ K.simplices | σ.dim ≤ d} | (σ.1.carrier ∩ U).Nonempty} ⊆
        Subtype.val ⁻¹' {σ : Simplex n | σ ∈ K.simplices ∧ (σ.carrier ∩ U).Nonempty} := by
      intro σ hσ
      exact ⟨σ.2.1, hσ⟩
    refine Set.Finite.subset ?_ this
    refine Set.Finite.preimage Subtype.val_injective.injOn ?_
    have hmap : {σ : Simplex n | σ ∈ K.simplices ∧ (σ.carrier ∩ U).Nonempty} =
        Subtype.val '' {σ : K.simplices | (σ.1.carrier ∩ U).Nonempty} := by
      ext σ
      simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
    rw [hmap]
    exact hfin.image Subtype.val
  face_closed := by
    intro σ τ ⟨hσK, hσd⟩ hface
    refine ⟨K.face_closed hσK hface, ?_⟩
    exact le_trans (Nat.sub_le_sub_right (Finset.card_le_card hface) 1) hσd
  inter_face := by
    intro σ₁ σ₂ ⟨h₁K, h₁d⟩ ⟨h₂K, _⟩ hne
    obtain ⟨τ, hτK, hτ₁, hτ₂, hτcar⟩ := K.inter_face h₁K h₂K hne
    refine ⟨τ, ⟨hτK, ?_⟩, hτ₁, hτ₂, hτcar⟩
    exact le_trans (Nat.sub_le_sub_right (Finset.card_le_card hτ₁) 1) h₁d

/-- The underlying polyhedron `|K|` of a Euclidean complex `K`. -/
def EuclideanComplex.polyhedron {n : ℕ} (K : EuclideanComplex n) : Set (EuclideanSpace ℝ (Fin n)) :=
  ⋃ σ ∈ K.simplices, σ.carrier

/-- A triangulation of a subset `X ⊆ ℝᵐ` by a Euclidean complex `K` in `ℝⁿ` is a homeomorphism
from `|K|` onto `X`. -/
structure Triangulation (n m : ℕ) (X : Set (EuclideanSpace ℝ (Fin m))) where
  complex : EuclideanComplex n
  toHomeomorph : complex.polyhedron ≃ₜ X

/-- `K'` is a subdivision of `K` if `|K'| = |K|` and every simplex of `K'` is contained in
some simplex of `K`. -/
def EuclideanComplex.IsSubdivision {n : ℕ} (K' K : EuclideanComplex n) : Prop :=
  K'.polyhedron = K.polyhedron ∧ ∀ σ' ∈ K'.simplices, ∃ σ ∈ K.simplices, σ'.carrier ⊆ σ.carrier

/-- A map `f : |K₁| → |K₂|` is simplicial if it maps vertices of `K₁` to vertices of `K₂`,
sends the vertex set of each simplex of `K₁` into the vertex set of a simplex of `K₂`, and
agrees with an affine map on each simplex of `K₁`. -/
def IsSimplicialMap {n m : ℕ} (K₁ : EuclideanComplex n) (K₂ : EuclideanComplex m)
    (f : K₁.polyhedron → K₂.polyhedron) : Prop :=
  ∀ σ ∈ K₁.simplices, ∃ τ ∈ K₂.simplices,
    ∃ A : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m),
      (∀ v ∈ σ.vertices, A v ∈ τ.vertices) ∧
      ∀ (x : K₁.polyhedron), x.1 ∈ σ.carrier → (f x : EuclideanSpace ℝ (Fin m)) = A x.1

/-- A continuous map `f : |K₁| → |K₂|` between polyhedra is piecewise linear (PL) if there
exist subdivisions `K₁'` of `K₁` and `K₂'` of `K₂` with respect to which `f` is simplicial. -/
def IsPLMap {n m : ℕ} (K₁ : EuclideanComplex n) (K₂ : EuclideanComplex m)
    (f : K₁.polyhedron → K₂.polyhedron) : Prop :=
  Continuous f ∧
  ∃ (K₁' : EuclideanComplex n) (K₂' : EuclideanComplex m)
    (h₁ : K₁'.IsSubdivision K₁) (h₂ : K₂'.IsSubdivision K₂),
    IsSimplicialMap K₁' K₂' (fun x =>
      ⟨(f ⟨x.1, h₁.1.subset x.2⟩).1,
       h₂.1.symm.subset (f ⟨x.1, h₁.1.subset x.2⟩).2⟩)

/-- A homeomorphism `f : |K₁| ≃ₜ |K₂|` is a PL homeomorphism if `f` is a PL map. -/
def IsPLHomeomorph {n m : ℕ} (K₁ : EuclideanComplex n) (K₂ : EuclideanComplex m)
    (f : K₁.polyhedron ≃ₜ K₂.polyhedron) : Prop :=
  IsPLMap K₁ K₂ f

end Moise


