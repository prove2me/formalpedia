-- Prove2me | Definitions.Def_PCB_alg
-- name    : PCB_alg
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T02:10:12.915416+00:00
-- url     : https://prove2.me/theorems/8710dc5d-f64e-44d2-b5ab-5ad9bae808dc
-- title:
--   The algebraic layer: positive cones, torsion, and convexity
-- statement:
--   The algebraic interface of the bi-ordering theory of the paper. The definition carries: the positive-cone predicate of Definition 1 - a subset of a group that does not contain the identity, is closed under products, contains no inverses of its elements, satisfies the trichotomy law that every non-identity element or its inverse lies in it, and is invariant under conjugation; such a subset determines a bi-invariant ordering, by the recipe that one element lies below another when the inverse of the first times the second lies in the cone; the torsion-free and no-generalized-torsion predicate of Corollary 5 - no positive power of a non-identity element is trivial, and no product of conjugates of a non-identity element is trivial, both consequences of bi-orderability; and the convexity predicate of Definition 7 - a subgroup is convex when every element lying strictly between two of its elements, in the ordering of the cone, belongs to it.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Definition 1, Corollary 5, Definition 7).

import Mathlib

/-!
# The algebraic layer: positive cones and orderability

The algebraic layer of the PCB mission, carrying the interface of Oscar
Ocampo and Juliana R. T. Theodoro de Lima, "Positive cones and bi-orderings
on almost-direct products of free groups" (arXiv:2209.04706, 2022): the
positive cone of Definition 1 - a conjugation-invariant subset closed under
products, containing neither the identity nor inverses, and satisfying the
trichotomy law, determining a bi-invariant ordering; the torsion-free and
no-generalized-torsion predicate of Corollary 5; and the convexity
predicate for subgroups of Definition 7.
-/

namespace PCB

/-- The subset P of G is a positive cone in the sense of Definition 1 of
the source paper: it does not contain the identity, it is closed under
products, it contains no inverses of its elements, every non-identity
element or its inverse lies in it, and it is invariant under conjugation.
Such a subset determines a bi-invariant ordering by g < h if and only if
the inverse of g times h lies in P. -/
def IsPositiveCone {G : Type*} [Group G] (P : Set G) : Prop :=
  (1 ∉ P) ∧ (∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) ∧ (∀ a ∈ P, a⁻¹ ∉ P) ∧
  (∀ g : G, g ≠ 1 → (g ∈ P ∨ g⁻¹ ∈ P)) ∧ (∀ a ∈ P, ∀ g : G, g * a * g⁻¹ ∈ P)

/-- The group G is torsion-free and has no generalized torsion: no
positive power of a non-identity element is trivial, and no product of
conjugates of a non-identity element is trivial. Both are consequences of
bi-orderability, as in Corollary 5 of the source paper. -/
def TorsionFreeNoGeneralizedTorsion (G : Type*) [Group G] : Prop :=
  (∀ g : G, g ≠ 1 → ∀ m : ℕ, 0 < m → g ^ m ≠ 1) ∧
  (∀ x : G, x ≠ 1 → ∀ L : List G, (L.map (fun g => g * x * g⁻¹)).prod ≠ 1)

/-- The subgroup H is convex with respect to the ordering determined by
the positive cone P: any element lying strictly between two elements of H
belongs to H, as in Definition 7 of the source paper. -/
def ConvexSubgroup {G : Type*} [Group G] (P : Set G) (H : Subgroup G) : Prop :=
  ∀ h1 ∈ H, ∀ h2 ∈ H, ∀ g : G, (h1⁻¹ * g ∈ P) → (g⁻¹ * h2 ∈ P) → g ∈ H

end PCB


