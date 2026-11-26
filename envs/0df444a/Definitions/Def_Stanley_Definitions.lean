-- Prove2me | Definitions.Def_Stanley_Definitions
-- name    : Stanley_Definitions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:55:20.156644+00:00
-- url     : https://prove2.me/theorems/46fad299-b431-5f7d-a4f8-cfef4db55fab
-- title:
--   Definitions
-- statement:
--   Definitions and structural lemmas for Definitions, from Juan Pablo Traverso Gianini (jtraverso/stanley; ChromaticPolynomial/ adapted under Apache-2.0 from anlucia/ChromaticPolynomial by Angelo Lucia; see pinned LICENSE and THIRD_PARTY.md)'s pinned Stanley's acyclic orientations and chromatic reciprocity development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/stanley/blob/48d36cbaa54d14443f99b57776ce65f1f31c8331/Stanley/Definitions.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.BigOperators.Finprod
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Stanley
open SimpleGraph Polynomial
variable {V : Type*} (G : SimpleGraph V)
noncomputable def chromaticPolynomial : ℤ[X] :=
  ∑ᶠ F : {F : Set (Sym2 V) // F ⊆ G.edgeSet},
    (-1 : ℤ[X]) ^ Nat.card F.val * X ^ Nat.card (fromEdgeSet F.val).ConnectedComponent
def IsAcyclicOrientation (r : V → V → Prop) : Prop :=
  (∀ u v, r u v → G.Adj u v) ∧
  (∀ u v, G.Adj u v → r u v ∨ r v u) ∧ WellFounded r
abbrev AcyclicOrientation := {r : V → V → Prop // IsAcyclicOrientation G r}
noncomputable def orientationCount : ℤ := Nat.card (AcyclicOrientation G)
@[ext] structure CompatiblePair (k : ℕ) where
  orientation : AcyclicOrientation G
  color : V → Fin k
  compatible : ∀ u v, orientation.val u v → color u ≤ color v
noncomputable def compatibleCount (k : ℕ) : ℤ := Nat.card (CompatiblePair G k)
end Stanley


