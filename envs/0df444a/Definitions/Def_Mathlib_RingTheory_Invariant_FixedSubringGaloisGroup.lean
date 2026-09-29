-- Prove2me | Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup
-- name    : Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/9b7e564d-e296-5854-a6b0-b636c60739db
-- title:
--   Fixed subring as Galois base of a faithful ring action
-- statement:
--   The standing context is a commutative ring $S$ together with a group $G$ acting on $S$ by ring automorphisms (a `MulSemiringAction`), the action being faithful. The single result, [`FixedPoints.isGaloisGroup_subring`](../def/Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup.html#L8), asserts that $G$ is a Galois group for the extension of $S$ over its fixed-point subring $S^G =$ `FixedPoints.subring S G`, i.e. that `IsGaloisGroup G (FixedPoints.subring S G) S` holds. Since `IsGaloisGroup` is a structure all of whose fields are propositions, the content of the statement is exactly the conjunction of its three fields, each verified here for the fixed subring: faithfulness of the $G$-action on $S$, which is the standing hypothesis; compatibility of the $G$-action with multiplication by scalars from the base, namely $g \cdot (r s) = r\,(g \cdot s)$ for $r \in S^G$ and $s \in S$, which follows because $g$ is a ring automorphism and fixes $r$; and the invariance condition `Algebra.IsInvariant` for the base $S^G$ in $S$ with respect to $G$, i.e. that every $b \in S$ with $g \cdot b = b$ for all $g \in G$ is the image of an element of the base — tautological here, as the base has been taken to be precisely the subring of $G$-fixed elements. Thus the lemma supplies, for an arbitrary faithful action of a group by ring automorphisms, the canonical instance of the Galois-group hypothesis used by the invariant-theoretic and ramification-theoretic machinery, with no auxiliary condition such as finiteness of $G$ or normality.
--
--   **Relation to Mathlib.** `IsGaloisGroup`, `FixedPoints.subring` and the invariance predicate are Mathlib notions; nothing new is defined here. The statement is the commutative-ring counterpart of the corresponding Mathlib fact for the fixed subfield of a faithful action on a field.
--
--   **Where it is used.** The instance is used where the decomposition and inertia theory of a group acting on a ring is applied, in particular in the identification of the cardinality of an inertia subgroup with a ramification index.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace FixedPoints

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
  [FaithfulSMul G S]

theorem isGaloisGroup_subring : IsGaloisGroup G (FixedPoints.subring S G) S where
  faithful := inferInstance
  commutes := ⟨fun g r s => by
    show g • ((r : S) * s) = (r : S) * (g • s); rw [smul_mul', r.2 g]⟩
  isInvariant := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩

end FixedPoints

/--
info: 'FixedPoints.isGaloisGroup_subring' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FixedPoints.isGaloisGroup_subring


