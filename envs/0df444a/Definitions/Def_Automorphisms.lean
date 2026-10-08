-- Prove2me | Definitions.Def_Automorphisms
-- name    : Automorphisms
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T04:41:26.075416+00:00
-- url     : https://prove2.me/theorems/ff1f57ea-79ba-44e1-b869-4e38f0255a51
-- title:
--   Graph automorphisms, vertex orbits, and local action
-- statement:
--   For a supplied finite graph, IsAut requires a permutation to preserve adjacency in both directions, and autSubgroup packages those permutations. The bundle identifies fixed vertices, induces a permutation on the neighbors of a fixed vertex, defines orbit equivalence and vertex transitivity, packages a two-orbit partition with within-orbit and separation conditions, and represents actual three-vertex cliques.
-- source:
--   Exact original Lean source: formalization/2026-10-03/automorphisms/Automorphisms.lean#L12-14, 16-27, 32-34, 132-136, 236-239, 431-433, 455-456, 458-465, 553-555; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 958c11a2ac95b43f12536e852e5d66a4b1917d56953aa0f9bfc2e09ff7df1791. Canonical generated Definition: Definitions/Def_Automorphisms.lean; generated SHA-256 fe3110aba66dd2fb4f660a19b833ba1ecc7a455fffbc94a1d347c58318ecfff1; Lab Git revision d00772b0fc789a0b159a3578e93645dce376150a, path fixtures/generated-project-definitions/Definitions/Def_Automorphisms.lean.

import Mathlib

set_option autoImplicit false

/-! Automorphisms and their vertex orbits for one literal graph. -/

namespace Conway99Formal.automorphisms

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A permutation preserving adjacency in the given graph. -/
def IsAut (σ : Equiv.Perm V) : Prop :=
  ∀ x y, G.Adj x y ↔ G.Adj (σ x) (σ y)

/-- Automorphisms of the given graph, with multiplication inherited from permutations. -/
def autSubgroup : Subgroup (Equiv.Perm V) where
  carrier := {σ | IsAut G σ}
  mul_mem' := by
    intro a b ha hb x y
    simp only [Equiv.Perm.mul_apply]
    exact (hb x y).trans (ha (b x) (b y))
  one_mem' := by intro x y; simp [IsAut]
  inv_mem' := by
    intro a ha x y
    have h := ha (a⁻¹ x) (a⁻¹ y)
    simpa using h.symm



/-- The actual fixed vertices of a permutation of this graph's vertex type. -/
def fixedSet (σ : Equiv.Perm V) : Finset V :=
  Finset.univ.filter fun x => σ x = x









/-- An automorphism fixing a vertex preserves its actual neighbor set. -/
theorem neighbor_mem_iff_apply (σ : Equiv.Perm V) (hσ : IsAut G σ)
    (x : V) (hx : σ x = x) (y : V) :
    y ∈ G.neighborFinset x ↔ σ y ∈ G.neighborFinset x := by
  simpa only [SimpleGraph.mem_neighborFinset, hx] using hσ x y









/-- The permutation induced on the neighbors of a fixed vertex. -/
def neighborPerm (σ : Equiv.Perm V) (hσ : IsAut G σ)
    (x : V) (hx : σ x = x) : Equiv.Perm (G.neighborFinset x) :=
  σ.subtypePerm (fun y => (neighbor_mem_iff_apply G σ hσ x hx y).symm)

















/-- Two vertices are equivalent under the automorphism group of this graph. -/
def SameOrbit (x y : V) : Prop :=
  ∃ σ : Equiv.Perm V, IsAut G σ ∧ σ x = y









/-- Predicate that the full automorphism group acts transitively on vertices. -/
def VertexTransitive : Prop := ∀ x y : V, SameOrbit G x y

/-- Data that the full automorphism group has exactly two vertex orbits. -/
structure TwoOrbitSplit where
  O : Finset V
  nonempty : O.Nonempty
  proper : ∃ x, x ∉ O
  inside : ∀ x ∈ O, ∀ y ∈ O, SameOrbit G x y
  outside : ∀ x, x ∉ O → ∀ y, y ∉ O → SameOrbit G x y
  separated : ∀ x ∈ O, ∀ y, y ∉ O → ¬ SameOrbit G x y















/-- A triangle is an actual three-point clique in the supplied graph. -/
def IsTriangle (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y






end Conway99Formal.automorphisms


