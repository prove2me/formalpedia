-- Prove2me | Definitions.Def_FanInSemigroup_IsGroupfree
-- name    : FanInSemigroup_IsGroupfree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:06.174419+00:00
-- url     : https://prove2.me/theorems/f2ff18e0-d4da-4c64-9143-74e256281ec2
-- title:
--   Groupfree semigroup
-- statement:
--   A semigroup $S$ is **groupfree** if it contains no nontrivial subgroup as a subset: there is no subset $H\subseteq S$ closed under the product, with an element $u\in H$ that is a two-sided identity on $H$, in which every element has an inverse relative to $u$, and which has an element other than $u$.
--
--   The identity of the subgroup need not be an identity of the semigroup. So the semigroup obtained from $\mathbb Z_2$ by adjoining a new identity is not groupfree, while the threshold semigroups and the carry semigroup are.
--
--   **Formalization Note** The definition is the literal one of the page. It does not go through Mathlib's subgroups or units, since those would tie the identity of $H$ to an identity of $S$; the equivalent condition $b^m=b^{m+1}$ for large $m$ is a milestone of the mission.
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, p.54

import Mathlib

set_option autoImplicit false

namespace FanInSemigroup

/-- The subset `H` of a semigroup, with the element `u`, is a nontrivial group under the
semigroup's product: `H` is closed under the product, `u ∈ H` is a two-sided identity on `H`,
every element of `H` has an inverse in `H`, and some element of `H` differs from `u`.

**Formalization Note.** Mathlib's `Subgroup` and units are not used, since `u` need not be an
identity of the semigroup. Chandra, Fortune, Lipton, STOC 1983, §2, p.54: "there is no requirement
that the identity of the subgroup be the same as the identity of the semigroup." -/
def IsNontrivialGroupIn {S : Type*} [Semigroup S] (H : Set S) (u : S) : Prop :=
  u ∈ H ∧ (∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) ∧ (∀ a ∈ H, u * a = a ∧ a * u = a) ∧
    (∀ a ∈ H, ∃ b ∈ H, a * b = u ∧ b * a = u) ∧ ∃ g ∈ H, g ≠ u

/-- Chandra, Fortune, Lipton, STOC 1983, §2, p.54: "A semigroup is groupfree if it contains no
nontrivial subgroup as a subset." -/
def IsGroupfree (S : Type*) [Semigroup S] : Prop :=
  ¬ ∃ (H : Set S) (u : S), IsNontrivialGroupIn H u

end FanInSemigroup


