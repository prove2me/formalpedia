-- Prove2me | Definitions.Def_CTB_alg
-- name    : CTB_alg
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T02:12:24.491766+00:00
-- url     : https://prove2.me/theorems/7aa14f91-dc83-47e7-a80b-722d1347a6c6
-- title:
--   The algebraic layer: torsion-freeness and two-power torsion
-- statement:
--   The algebraic interface of the crystallographic realization theory of the paper. The definition carries: the torsion-free predicate for the Bieberbach subgroups - the fundamental groups of compact flat manifolds - no positive power of a non-identity element is the identity; and the two-power torsion predicate for the elements of the holonomy groups - some power of two annihilates the element - through which the preimage construction of Proposition 2.5 is expressed: the full preimage of a finite 2-group of holonomies is Bieberbach, using the absence of even-order torsion in the braid quotient established in the companion paper.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 2 (Proposition 2.5).

import Mathlib

/-!
# The algebraic layer: torsion-freeness and two-power torsion

The algebraic layer of the CTB mission, carrying the interface of Oscar
Ocampo, "Crystallographic quotients of Artin braid groups and torus bundles
over flat 3-manifolds" (arXiv:2610.20478, 2026): the torsion-free
predicate for the Bieberbach subgroups - the fundamental groups of compact
flat manifolds - and the two-power torsion predicate for the elements of
the holonomy groups, through which the preimage construction of
Proposition 2.5 - the full preimage of a finite 2-group of holonomies is
Bieberbach - is expressed, using the absence of even-order torsion in the
braid quotient established in the companion paper.
-/

namespace CTB

/-- The group G is torsion-free: no positive power of a non-identity
element is the identity. -/
def TorsionFree (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∀ m : ℕ, 0 < m → g ^ m ≠ 1

/-- The element g is of two-power order: some power of two annihilates
it. A finite group all of whose elements satisfy this predicate is a
2-group, and the preimage of such a holonomy group is Bieberbach by
Proposition 2.5 of the source paper. -/
def IsTwoTorsion {G : Type*} [Group G] (g : G) : Prop :=
  ∃ j : ℕ, g ^ 2 ^ j = 1

end CTB


