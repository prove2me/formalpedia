-- Prove2me | Definitions.Def_CTB_tor
-- name    : CTB_tor
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T02:12:52.771925+00:00
-- url     : https://prove2.me/theorems/5afb821c-ac16-4b52-976e-f47035339b80
-- title:
--   The world layer: the idealized crystallographic braid quotient
-- statement:
--   The idealized world of the crystallographic braid quotient. The definition carries: the quotient group with its translation lattice - free Abelian of rank the number of unordered pairs of strings, normal, commutative, and equal to the kernel of the holonomy projection onto the symmetric group; the absence of nontrivial two-power torsion elements, the companion paper's Theorem 2; and the realization predicate, which records that a pair of subgroups of the quotient with a homomorphism realizes an abstract model group - a fundamental group of a compact flat 3-manifold - as a torus-bundle quotient: the kernel lies in the lattice and in the total-space subgroup, is free Abelian of rank three less than the lattice rank, is exactly the kernel of the homomorphism on the total-space subgroup, and the homomorphism maps the total-space subgroup onto the model group. This is the shape of the realizations of the theorems of Sections 3 and 4 of the paper.
-- source:
--   O. Ocampo, Crystallographic quotients of Artin braid groups and torus bundles over flat 3-manifolds, arXiv:2610.20478 (2026), Section 2 (the crystallographic quotient, its translation lattice, and the holonomy projection).

import Mathlib
import Definitions.Def_CTB_alg

/-!
# The world layer: the idealized crystallographic braid quotient

The world layer of the CTB mission: the idealized quotient of the Artin
braid group on n strings by the commutator subgroup of its pure braid
group, as in the companion paper of the source paper of Oscar Ocampo. The
world carries: the translation lattice - free Abelian of rank the number
of unordered pairs of strings, normal, and equal to the kernel of the
holonomy projection onto the symmetric group; and the absence of nontrivial
two-power torsion elements (the companion paper, Theorem 2). The ten model
groups of Wolf's classification of the compact flat 3-manifolds - the torus
G1, the four orientable classes G2 through G6 with cyclic, Klein four, and
Hantzsche-Wendt holonomy, and the four non-orientable classes B1 through
B4 - appear as abstract groups in the realization theorems. The
realization predicate records that a pair of subgroups of the quotient
with a homomorphism realizes a model group as a torus-bundle quotient.
-/

namespace CTB

/-- The idealized world of the crystallographic braid quotient: the group
Q with its translation lattice, free Abelian of rank the number of
unordered pairs of strings and equal to the kernel of the holonomy
projection, without nontrivial two-power torsion elements. -/
structure CrystallographicBraidWorld (n : ℕ) (Q : Type*) [Group Q] where
  lattice : Subgroup Q
  latticeNormal : lattice.Normal
  latticeComm : ∀ x ∈ lattice, ∀ y ∈ lattice, x * y = y * x
  latticeIso : (↥lattice) ≃* Multiplicative (Fin (Nat.choose n 2) → ℤ)
  hol : Q →* Equiv.Perm (Fin n)
  holKer : MonoidHom.ker hol = lattice
  noEvenTorsion : ∀ g : Q, IsTwoTorsion g → g = 1

/-- The data of a torus-bundle realization of the abstract group G - a
model of the fundamental group of a compact flat 3-manifold - as a
quotient of subgroups of the crystallographic braid quotient: the kernel
Ker lies in the translation lattice and in the total space subgroup Gam,
is free Abelian of rank the lattice rank minus three, and is exactly the
kernel of the homomorphism f on Gam, while f maps Gam onto G. This is the
shape of the realizations of Theorems 3.1 through 3.9 and 4.1 through 4.5
of the source paper. -/
def IsTorusBundleRealization {n : ℕ} {Q G : Type*} [Group Q] [Group G]
    (W : CrystallographicBraidWorld n Q) (Gam Ker : Subgroup Q) (f : Q →* G) : Prop :=
  (∀ x ∈ Ker, x ∈ W.lattice) ∧ (∀ x ∈ Ker, x ∈ Gam) ∧
  Nonempty ((↥Ker) ≃* Multiplicative (Fin (Nat.choose n 2 - 3) → ℤ)) ∧
  (∀ x ∈ Ker, f x = 1) ∧ (∀ x ∈ Gam, f x = 1 → x ∈ Ker) ∧
  (∀ y : G, ∃ x, x ∈ Gam ∧ f x = y)

end CTB


