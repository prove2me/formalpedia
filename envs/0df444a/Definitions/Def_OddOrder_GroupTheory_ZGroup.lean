-- Prove2me | Definitions.Def_OddOrder_GroupTheory_ZGroup
-- name    : OddOrder_GroupTheory_ZGroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:29.819662+00:00
-- url     : https://prove2.me/theorems/4c1e6993-ac14-4c89-aa0f-32d513ab99b8
-- title:
--   Z-groups (every Sylow subgroup cyclic)
-- statement:
--   A shared module defining Z-groups, finite groups all of whose Sylow subgroups are cyclic, as used in Bender–Glauberman, *Local Analysis for the Odd Order Theorem* in §10 (Lemma 10.4(b)) and §3 (Theorem 3.6). The repository keeps its own predicate and bridges it to the Mathlib `IsZGroup` class, which has the same defining condition.
--
--   The main declaration: `IsZGroup` (Z-group: a group all of whose Sylow subgroups are cyclic).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/ZGroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ZGroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.ZGroup

namespace OddOrder.GroupTheory

/-- **Z-group**: a group all of whose Sylow subgroups are cyclic. -/
def IsZGroup (G : Type*) [Group G] : Prop :=
  ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsCyclic ↥(P : Subgroup G)

/-- The repository `IsZGroup` predicate agrees with `mathlib`'s `IsZGroup` class: both say that
every Sylow subgroup is cyclic.  This bridge unlocks the `mathlib` Z-group API (subgroup/quotient
closure, `exponent_eq_card`, `IsPGroup.isCyclic_of_isZGroup`). -/
theorem isZGroup_iff_mathlib {G : Type*} [Group G] :
    IsZGroup G ↔ _root_.IsZGroup G :=
  ⟨fun h => (isZGroup_iff G).mpr h, fun h => (isZGroup_iff G).mp h⟩

/-- A nontrivial Z-group in which every element has order dividing the prime `p` has order exactly
`p`.  (BG Theorem 3.6 (3.19)/(3.31): a Z-group contains no elementary abelian subgroup of order
`p²`.)  Proof: the group is its own Sylow `p`-subgroup, hence cyclic, so its order — equal to its
exponent (`IsZGroup.exponent_eq_card`) — divides `p`; nontriviality rules out order `1`. -/
theorem card_eq_prime_of_isZGroup_exponent_dvd {G : Type*} [Group G] [Finite G] [_root_.IsZGroup G]
    [Nontrivial G] {p : ℕ} (hp : p.Prime) (hexp : ∀ g : G, g ^ p = 1) :
    Nat.card G = p := by
  have hdvd : Nat.card G ∣ p := by
    rw [← IsZGroup.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial G›).ne'
  · exact hp'

/-- **BG Theorem 3.6 form** of `card_eq_prime_of_isZGroup_exponent_dvd`.  If `A ≤ Z` with `Z` a
Z-group, `A` nontrivial, and every element of `A` has order dividing the prime `p`, then `|A| = p`.

Used at BG (3.19) (`A = C_V(R₀) ≤ C_H(R₀)`, `V` elementary abelian `p`-group) and at (3.31)
(`A = C_K(R) ≤ C_H(R)`, `K` of exponent `q`). -/
theorem card_eq_prime_of_le_isZGroup {G : Type*} [Group G] [Finite G] {Z : Subgroup G}
    (hZ : IsZGroup ↥Z) {A : Subgroup G} (hAZ : A ≤ Z) {p : ℕ} (hp : p.Prime)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hA : A ≠ ⊥) :
    Nat.card ↥A = p := by
  have : _root_.IsZGroup ↥Z := isZGroup_iff_mathlib.mp hZ
  have : _root_.IsZGroup ↥A := IsZGroup.of_injective (Subgroup.inclusion_injective hAZ)
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  have hexp' : ∀ a : ↥A, a ^ p = 1 := fun a =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hexp (a : G) a.2)
  exact card_eq_prime_of_isZGroup_exponent_dvd hp hexp'

end OddOrder.GroupTheory


