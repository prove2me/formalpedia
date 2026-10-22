-- Prove2me | Definitions.Def_PCB_tor
-- name    : PCB_tor
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T02:10:45.313985+00:00
-- url     : https://prove2.me/theorems/6c547bc5-c5a8-4abf-b290-e0cc3aa417af
-- title:
--   The world layer: the idealized almost-direct product of free groups with its lexicographic cone
-- statement:
--   The idealized world of an almost-direct product of free groups. The definition carries: the free factors as an indexed family of groups, each equipped with its Magnus-type positive cone satisfying the positive-cone predicate; the normal-form data - the assembly of a tuple of components into an element of the ambient group and the extraction of the components of an element, the two maps inverse to each other; the conjugation action of the ambient group on each free factor, preserving the cones - the idealized form of the almost-direct property, by which the action of each factor on the abelianization of the preceding ones is trivial - with the conjugation of an element acting componentwise in the normal form; and the canonical filtration subgroups, characterized as the elements whose components vanish above the given index. The definition also carries the lexicographic cone of Definition 2 - the elements whose highest nontrivial normal-form component is positive in the Magnus-type ordering of the corresponding free factor - and the embedding of a single free factor into the product, placing the given element in its slot and the identities in the others.
-- source:
--   O. Ocampo, J. R. T. Theodoro de Lima, Positive cones and bi-orderings on almost-direct products of free groups, arXiv:2209.04706 (2022), Section 2 (Definition 2, the normal-form decomposition, and the canonical subgroups).

import Mathlib
import Definitions.Def_PCB_alg

/-!
# The world layer: the idealized almost-direct product of free groups

The world layer of the PCB mission: the idealized almost-direct product of
free groups of Section 2 of the source paper of Oscar Ocampo and Juliana
R. T. Theodoro de Lima. The world carries: the free factors as an indexed
family of groups, each equipped with its Magnus-type positive cone; the
normal-form decomposition - the assembly of a tuple of components into an
element of G and the extraction of the components, inverse to each other;
the conjugation action of G on each factor, preserving the cones, through
which the almost-direct property - the conjugation action is trivial on
the abelianization of each factor, hence preserves the Magnus-type
ordering - is idealized; and the canonical filtration subgroups,
characterized as the elements whose components vanish above the given
index; together with the lexicographic cone of Definition 2 and the
embedding of a single factor.
-/

namespace PCB

/-- The idealized world of an almost-direct product of free groups: the
group G with its k free factors F, each carrying its Magnus-type positive
cone; the normal-form data assembling component tuples into elements and
extracting components back, inverse to each other; the cone-preserving
conjugation action on each factor, with the conjugation of an element
acting componentwise; and the canonical filtration subgroups of elements
whose components vanish above a given index. -/
structure AlmostDirectProductWorld (k : ℕ) (G : Type*) [Group G]
    (F : Fin k → Type*) [∀ j, Group (F j)] where
  cone : ∀ j : Fin k, Set (F j)
  conePos : ∀ j : Fin k, IsPositiveCone (cone j)
  nf : G → ∀ j : Fin k, F j
  assemble : (∀ j : Fin k, F j) → G
  assemble_nf : ∀ g : G, assemble (nf g) = g
  nf_assemble : ∀ x : (∀ j : Fin k, F j), nf (assemble x) = x
  conjOn : G → ∀ j : Fin k, F j → F j
  conjOn_cone : ∀ (x : G) (j : Fin k) (f : F j), f ∈ cone j → conjOn x j f ∈ cone j
  nf_conj : ∀ (x g : G) (j : Fin k), nf (x * g * x⁻¹) j = conjOn x j (nf g j)
  tower : Fin k → Subgroup G
  towerMem : ∀ (j : Fin k) (g : G), g ∈ tower j ↔ ∀ i : Fin k, j < i → nf g i = 1

/-- The lexicographic positive cone of Definition 2 of the source paper:
the elements of G whose highest nontrivial component in the normal form is
positive with respect to the Magnus-type ordering of the corresponding
free factor. -/
def lexCone {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) : Set G :=
  {g : G | ∃ j : Fin k, (∀ i : Fin k, j < i → W.nf g i = 1) ∧ W.nf g j ∈ W.cone j}

/-- The embedding of the j-th free factor into G: the element with the
given component in the j-th slot and the identity in all other slots. -/
def embedFactor {k : ℕ} {G : Type*} [Group G] {F : Fin k → Type*} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) (j : Fin k) (f : F j) : G :=
  W.assemble (fun i => if h : i = j then h ▸ f else 1)

end PCB


